#import <Foundation/Foundation.h>
#import <CoreFoundation/CoreFoundation.h>
#import <CFNetwork/CFNetwork.h>
#import <UIKit/UIWebView.h>
#import <objc/runtime.h>
#import <objc/message.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <netdb.h>
#include <errno.h>
#include <ctype.h>
#include <dns_sd.h>
#include <pthread.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <stdatomic.h>
#include "fishhook.h"
#import "domain_list.h"

#define DNS_CACHE_SIZE 2048
#define MAX_DOMAIN_LENGTH 256
#define CACHE_MUTEX_COUNT 64
#define BLOOM_FILTER_SIZE (1 << 20)
#define BLOOM_FILTER_HASH_COUNT 4

typedef struct dns_cache_entry {
    char domain[MAX_DOMAIN_LENGTH];
    int blocked;
    uint64_t last_access;
    uint32_t hash;
    struct dns_cache_entry *next;
} dns_cache_entry_t;

typedef struct RadixChild {
    unsigned char c;
    struct RadixNode *child;
} RadixChild;

typedef struct RadixNode {
    RadixChild *children;
    int childCount;
    int capacity;
    uint8_t is_end;
} RadixNode;

static _Atomic(dns_cache_entry_t *) *dns_cache = NULL;
static uint64_t cache_access_counter = 0;
static pthread_mutex_t cache_mutex[CACHE_MUTEX_COUNT];
static pthread_once_t init_once = PTHREAD_ONCE_INIT;
static dispatch_queue_t lookup_queue;
static RadixNode *domain_trie_root = NULL;
static uint8_t *bloom_filter = NULL;

static int (*orig_getaddrinfo)(const char *restrict, const char *restrict,
                               const struct addrinfo *restrict,
                               struct addrinfo **restrict) = NULL;
static struct hostent *(*orig_gethostbyname)(const char *) = NULL;
static struct hostent *(*orig_gethostbyname2)(const char *) = NULL;
static int (*orig_connect)(int, const struct sockaddr *, socklen_t) = NULL;
static ssize_t (*orig_sendto)(int, const void *, size_t, int, const struct sockaddr *, socklen_t) = NULL;
static DNSServiceErrorType (*orig_DNSServiceQueryRecord)(DNSServiceRef *sdRef,
                                                         DNSServiceFlags flags,
                                                         uint32_t interfaceIndex,
                                                         const char *fullname,
                                                         uint16_t rrtype,
                                                         uint16_t rrclass,
                                                         DNSServiceQueryRecordReply callBack,
                                                         void *context) = NULL;

static Boolean (*orig_CFNetServiceSetClient)(CFNetServiceRef theService,
                                             CFNetServiceClientCallBack clientCB,
                                             CFNetServiceClientContext *clientContext) = NULL;
static CFNetServiceRef (*orig_CFNetServiceCreate)(CFAllocatorRef alloc,
                                                 CFStringRef domain,
                                                 CFStringRef serviceType,
                                                 CFStringRef name,
                                                 SInt32 port) = NULL;
static Boolean (*orig_CFNetServiceResolveWithTimeout)(CFNetServiceRef theService,
                                                      CFTimeInterval timeout,
                                                      CFStreamError *error) = NULL;
static CFReadStreamRef (*orig_CFStreamCreateForHTTPRequest)(CFAllocatorRef alloc,
                                                           CFHTTPMessageRef request) = NULL;
static CFHTTPMessageRef (*orig_CFHTTPMessageCreateRequest)(CFAllocatorRef alloc,
                                                          CFStringRef requestMethod,
                                                          CFURLRef url,
                                                          CFStringRef httpVersion) = NULL;

static IMP orig_NSNetServiceInitWithDomain = NULL;
static IMP orig_NSNetServiceInitWithDomainService = NULL;
static IMP orig_NSNetServiceResolve = NULL;
static IMP orig_NSURLSessionDataTaskWithURL = NULL;
static IMP orig_NSURLSessionDataTaskWithRequest = NULL;
static IMP orig_NSURLConnectionSendAsynchronousRequest = NULL;
static IMP orig_UIWebViewLoadRequest = NULL;
static IMP orig_WKWebViewLoadRequest = NULL;

static inline int search_domain(const RadixNode *root, const char *hostname);
static int is_domain_blocked(const char *hostname);
static void dns_cache_insert(const char *domain, int blocked);
static int dns_cache_lookup(const char *domain, int *blocked);
static BOOL is_url_blocked(NSURL *url);

static inline void CFStringToBuffer(CFStringRef string, char *buffer, size_t bufferSize) {
    if (string && buffer && bufferSize > 0) {
        if (!CFStringGetCString(string, buffer, bufferSize, kCFStringEncodingUTF8)) {
            buffer[0] = '\0';
        }
    } else if(buffer && bufferSize > 0) {
        buffer[0] = '\0';
    }
}

__attribute__((always_inline))
static inline uint32_t fnv1a_hash(const char *str) {
    uint32_t hash = 2166136261u;
    for (; *str; ++str) {
        hash ^= (uint8_t)tolower(*str);
        hash *= 16777619;
    }
    return hash;
}

static void bloom_filter_init(void) {
    size_t bytes = BLOOM_FILTER_SIZE / 8;
    bloom_filter = (uint8_t *)calloc(bytes, 1);
}

__attribute__((always_inline))
static inline uint32_t bloom_hash1(const char *str) {
    return fnv1a_hash(str);
}

__attribute__((always_inline))
static inline uint32_t bloom_hash2(const char *str) {
    uint32_t hash = 5381;
    for (; *str; str++) {
        hash = ((hash << 5) + hash) + (unsigned char)tolower(*str);
    }
    return hash;
}

static void bloom_filter_add(const char *str) {
    if (!str || !bloom_filter) return;
    uint32_t h1 = bloom_hash1(str);
    uint32_t h2 = bloom_hash2(str);
    for (int i = 0; i < BLOOM_FILTER_HASH_COUNT; i++) {
        uint32_t combined = h1 + i * h2;
        uint32_t bitIndex = combined % BLOOM_FILTER_SIZE;
        bloom_filter[bitIndex / 8] |= (1 << (bitIndex % 8));
    }
}

__attribute__((always_inline))
static inline int bloom_filter_check(const char *str) {
    if (!str || !bloom_filter) return 0;
    uint32_t h1 = bloom_hash1(str);
    uint32_t h2 = bloom_hash2(str);
    for (int i = 0; i < BLOOM_FILTER_HASH_COUNT; i++) {
        uint32_t combined = h1 + i * h2;
        uint32_t bitIndex = combined % BLOOM_FILTER_SIZE;
        if ((bloom_filter[bitIndex / 8] & (1 << (bitIndex % 8))) == 0) {
            return 0;
        }
    }
    return 1;
}

static void dns_cache_init(void) {
    dns_cache = calloc(DNS_CACHE_SIZE, sizeof(_Atomic(dns_cache_entry_t *)));
    for (int i = 0; i < CACHE_MUTEX_COUNT; i++) {
        pthread_mutex_init(&cache_mutex[i], NULL);
    }
    lookup_queue = dispatch_queue_create("net.gammesofts.ios.adblock.lookup", DISPATCH_QUEUE_CONCURRENT);
}

static int dns_cache_lookup(const char *domain, int *blocked) {
    if (!domain) return 0;
    
    uint32_t hash = fnv1a_hash(domain);
    unsigned int bucket = hash % DNS_CACHE_SIZE;
    dns_cache_entry_t *entry = atomic_load_explicit(&dns_cache[bucket], memory_order_acquire);
    while (entry) {
        if (entry->hash == hash && strcmp(entry->domain, domain) == 0) {
            __atomic_fetch_add(&cache_access_counter, 1, __ATOMIC_RELAXED);
            *blocked = entry->blocked;
            return 1;
        }
        entry = entry->next;
    }
    return 0;
}

static void dns_cache_insert(const char *domain, int blocked) {
    if (!domain) return;
    
    uint32_t hash = fnv1a_hash(domain);
    unsigned int bucket = hash % DNS_CACHE_SIZE;
    unsigned int mutex_idx = hash % CACHE_MUTEX_COUNT;
    
    pthread_mutex_lock(&cache_mutex[mutex_idx]);
    dns_cache_entry_t *entry = atomic_load_explicit(&dns_cache[bucket], memory_order_relaxed);
    while (entry) {
        if (entry->hash == hash && strcmp(entry->domain, domain) == 0) {
            entry->blocked = blocked;
            entry->last_access = __atomic_fetch_add(&cache_access_counter, 1, __ATOMIC_RELAXED);
            pthread_mutex_unlock(&cache_mutex[mutex_idx]);
            return;
        }
        entry = entry->next;
    }
    dns_cache_entry_t *new_entry = malloc(sizeof(dns_cache_entry_t));
    strlcpy(new_entry->domain, domain, MAX_DOMAIN_LENGTH);
    new_entry->blocked = blocked;
    new_entry->hash = hash;
    new_entry->last_access = __atomic_fetch_add(&cache_access_counter, 1, __ATOMIC_RELAXED);
    new_entry->next = atomic_load_explicit(&dns_cache[bucket], memory_order_relaxed);
    atomic_store_explicit(&dns_cache[bucket], new_entry, memory_order_release);
    pthread_mutex_unlock(&cache_mutex[mutex_idx]);
}

static RadixNode *create_radix_node(void) {
    RadixNode *node = calloc(1, sizeof(RadixNode));
    return node;
}

static RadixNode *get_child(RadixNode *node, unsigned char c) {
    for (int i = 0; i < node->childCount; i++) {
        if (node->children[i].c == c) {
            return node->children[i].child;
        }
    }
    return NULL;
}

static RadixNode *add_child(RadixNode *node, unsigned char c) {
    if (node->childCount == node->capacity) {
        int newCapacity = (node->capacity == 0) ? 4 : node->capacity * 2;
        node->children = realloc(node->children, newCapacity * sizeof(RadixChild));
        node->capacity = newCapacity;
    }
    RadixNode *child = create_radix_node();
    node->children[node->childCount].c = c;
    node->children[node->childCount].child = child;
    node->childCount++;
    return child;
}

static void radix_insert(RadixNode *root, const char *domain) {
    if (!root || !domain) return;
    int len = (int)strlen(domain);
    RadixNode *node = root;
    for (int i = len - 1; i >= 0; i--) {
        unsigned char c = (unsigned char)tolower(domain[i]);
        RadixNode *child = get_child(node, c);
        if (!child) {
            child = add_child(node, c);
        }
        node = child;
    }
    node->is_end = 1;
}

static void build_domain_trie(void) {
    const char *list = embedded_domain_list;
    if (!list) return;
    
    domain_trie_root = create_radix_node();
    bloom_filter_init();
    
    const char *start = list;
    const char *end;
    while (*start) {
        end = strchr(start, '\n');
        if (!end) end = start + strlen(start);
        int len = end - start;
        if (len > 0 && len < MAX_DOMAIN_LENGTH) {
            char domain[MAX_DOMAIN_LENGTH];
            memcpy(domain, start, len);
            domain[len] = '\0';
            radix_insert(domain_trie_root, domain);
            bloom_filter_add(domain);
        }
        if (*end == '\0') break;
        start = end + 1;
    }
}

static int is_domain_blocked(const char *hostname) {
    if (!hostname) return 0;
    
    const char *p = hostname;
    int bloom_hit = 0;
    while (p) {
        if (bloom_filter_check(p)) {
            bloom_hit = 1;
            break;
        }
        p = strchr(p, '.');
        if (p) p++;
    }
    if (!bloom_hit) return 0;
    
    int cached;
    if (dns_cache_lookup(hostname, &cached)) {
        return cached;
    }
    
    p = hostname;
    int blocked = 0;
    while (p) {
        if (search_domain(domain_trie_root, p)) {
            blocked = 1;
            break;
        }
        p = strchr(p, '.');
        if (p) p++;
    }
    dns_cache_insert(hostname, blocked);
    return blocked;
}

static inline int search_domain(const RadixNode *root, const char *hostname) {
    if (!root || !hostname) return 0;
    int len = (int)strlen(hostname);
    const RadixNode *node = root;
    for (int i = len - 1; i >= 0; i--) {
        unsigned char c = (unsigned char)tolower(hostname[i]);
        const RadixNode *child = NULL;
        for (int j = 0; j < node->childCount; j++) {
            if (node->children[j].c == c) {
                child = node->children[j].child;
                break;
            }
        }
        if (!child) {
            if (c == '.' && node->is_end) {
                return 1;
            }
            return 0;
        }
        node = child;
        if (node->is_end && (i == 0 || hostname[i - 1] == '.')) {
            return 1;
        }
    }
    return node->is_end;
}

static BOOL is_url_blocked(NSURL *url) {
    if (!url) return NO;
    NSString *host = url.host;
    if (!host) return NO;
    const char *hostStr = [host UTF8String];
    if (!hostStr) return NO;
    return is_domain_blocked(hostStr) ? YES : NO;
}

static int extract_host_from_sockaddr(const struct sockaddr *addr, char *host, size_t hostlen) {
    if (addr->sa_family == AF_INET) {
        struct sockaddr_in *sin = (struct sockaddr_in *)addr;
        if (!inet_ntop(AF_INET, &sin->sin_addr, host, hostlen)) {
            return 0;
        }
        return 1;
    } else if (addr->sa_family == AF_INET6) {
        struct sockaddr_in6 *sin6 = (struct sockaddr_in6 *)addr;
        if (!inet_ntop(AF_INET6, &sin6->sin6_addr, host, hostlen)) {
            return 0;
        }
        return 1;
    }
    return 0;
}

static int resolve_address_to_hostname(const struct sockaddr *addr, char *hostname, size_t hostlen) {
    if (!addr || !hostname || hostlen < 1) return 0;
    static pthread_mutex_t resolve_mutex = PTHREAD_MUTEX_INITIALIZER;
    static NSCache *resolveCache = nil;
    static dispatch_once_t onceToken;
    dispatch_once(&onceToken, ^{
        resolveCache = [[NSCache alloc] init];
        resolveCache.countLimit = DNS_CACHE_SIZE;
    });
    
    char ipstr[INET6_ADDRSTRLEN] = {0};
    if (!extract_host_from_sockaddr(addr, ipstr, sizeof(ipstr))) {
        return 0;
    }
    NSString *ipKey = [NSString stringWithUTF8String:ipstr];
    
    pthread_mutex_lock(&resolve_mutex);
    NSString *cachedName = [resolveCache objectForKey:ipKey];
    if (cachedName) {
        strlcpy(hostname, [cachedName UTF8String], hostlen);
        pthread_mutex_unlock(&resolve_mutex);
        return 1;
    }
    pthread_mutex_unlock(&resolve_mutex);
    
    struct addrinfo hints, *result = NULL;
    memset(&hints, 0, sizeof(hints));
    hints.ai_family = addr->sa_family;
    hints.ai_flags = AI_CANONNAME;
    hints.ai_socktype = SOCK_STREAM;
    
    int error = getaddrinfo(ipstr, NULL, &hints, &result);
    if (error != 0 || !result) {
        strlcpy(hostname, ipstr, hostlen);
        return 1;
    }
    
    NSString *canonName = nil;
    if (result->ai_canonname && strlen(result->ai_canonname) > 0) {
        canonName = [NSString stringWithUTF8String:result->ai_canonname];
    } else {
        canonName = [NSString stringWithUTF8String:ipstr];
    }
    
    pthread_mutex_lock(&resolve_mutex);
    [resolveCache setObject:canonName forKey:ipKey];
    pthread_mutex_unlock(&resolve_mutex);
    
    strlcpy(hostname, [canonName UTF8String], hostlen);
    if (result) {
        freeaddrinfo(result);
    }
    return 1;
}

int my_getaddrinfo(const char *restrict node, const char *restrict service,
                   const struct addrinfo *restrict hints,
                   struct addrinfo **restrict res) {
    if (node && is_domain_blocked(node)) {
        struct addrinfo *dummy = malloc(sizeof(struct addrinfo));
        if (!dummy) return EAI_MEMORY;
        memset(dummy, 0, sizeof(struct addrinfo));
        dummy->ai_family = AF_INET;
        dummy->ai_socktype = SOCK_STREAM;
        dummy->ai_protocol = IPPROTO_TCP;
        dummy->ai_addrlen = sizeof(struct sockaddr_in);
        struct sockaddr_in *addr = malloc(sizeof(struct sockaddr_in));
        if (!addr) {
            free(dummy);
            return EAI_MEMORY;
        }
        memset(addr, 0, sizeof(struct sockaddr_in));
        addr->sin_family = AF_INET;
        addr->sin_port = 0;
        addr->sin_addr.s_addr = htonl(0x7F000001);
        dummy->ai_addr = (struct sockaddr *)addr;
        dummy->ai_next = NULL;
        *res = dummy;
        return 0;
    }
    return orig_getaddrinfo(node, service, hints, res);
}

struct hostent *my_gethostbyname(const char *name) {
    if (name && is_domain_blocked(name)) {
        static struct hostent dummy;
        static char *dummy_aliases[] = { NULL };
        static char *dummy_addr_list[2];
        static struct in_addr dummy_in_addr;
        dummy_in_addr.s_addr = htonl(0x7F000001);
        dummy_addr_list[0] = (char *)&dummy_in_addr;
        dummy_addr_list[1] = NULL;
        dummy.h_name = (char *)name;
        dummy.h_aliases = dummy_aliases;
        dummy.h_addrtype = AF_INET;
        dummy.h_length = sizeof(struct in_addr);
        dummy.h_addr_list = dummy_addr_list;
        return &dummy;
    }
    return orig_gethostbyname(name);
}

struct hostent *my_gethostbyname2(const char *name, int af) {
    if (name && is_domain_blocked(name)) {
        if (af == AF_INET) {
            static struct hostent dummy;
            static char *dummy_aliases[] = { NULL };
            static char *dummy_addr_list[2];
            static struct in_addr dummy_in_addr;
            dummy_in_addr.s_addr = htonl(0x7F000001);
            dummy_addr_list[0] = (char *)&dummy_in_addr;
            dummy_addr_list[1] = NULL;
            dummy.h_name = (char *)name;
            dummy.h_aliases = dummy_aliases;
            dummy.h_addrtype = AF_INET;
            dummy.h_length = sizeof(struct in_addr);
            dummy.h_addr_list = dummy_addr_list;
            return &dummy;
        } else {
            return NULL;
        }
    }
    return orig_gethostbyname2(name);
}

int my_connect(int socket, const struct sockaddr *address, socklen_t address_len) {
    if (address) {
        char hostname[NI_MAXHOST] = {0};
        if (resolve_address_to_hostname(address, hostname, sizeof(hostname)) &&
            is_domain_blocked(hostname)) {
            errno = EHOSTUNREACH;
            return -1;
        }
    }
    return orig_connect(socket, address, address_len);
}

ssize_t my_sendto(int socket, const void *buffer, size_t length, int flags,
                  const struct sockaddr *dest_addr, socklen_t dest_len) {
    if (dest_addr) {
        char hostname[NI_MAXHOST] = {0};
        if (resolve_address_to_hostname(dest_addr, hostname, sizeof(hostname)) &&
            is_domain_blocked(hostname)) {
            errno = EHOSTUNREACH;
            return -1;
        }
    }
    return orig_sendto(socket, buffer, length, flags, dest_addr, dest_len);
}

DNSServiceErrorType my_DNSServiceQueryRecord(DNSServiceRef *sdRef,
                                             DNSServiceFlags flags,
                                             uint32_t interfaceIndex,
                                             const char *fullname,
                                             uint16_t rrtype,
                                             uint16_t rrclass,
                                             DNSServiceQueryRecordReply callBack,
                                             void *context) {
    if (fullname && is_domain_blocked(fullname)) {
        return kDNSServiceErr_NoError;
    }
    return orig_DNSServiceQueryRecord(sdRef, flags, interfaceIndex, fullname,
                                      rrtype, rrclass, callBack, context);
}

CFNetServiceRef my_CFNetServiceCreate(CFAllocatorRef alloc,
                                      CFStringRef domain,
                                      CFStringRef serviceType,
                                      CFStringRef name,
                                      SInt32 port) {
    char domainBuf[MAX_DOMAIN_LENGTH] = {0};
    char nameBuf[MAX_DOMAIN_LENGTH] = {0};
    if (domain) {
        CFStringToBuffer(domain, domainBuf, MAX_DOMAIN_LENGTH);
        if (domainBuf[0] && is_domain_blocked(domainBuf)) {
            CFStringRef dummyDomain = CFSTR("127.0.0.1");
            return orig_CFNetServiceCreate(alloc, dummyDomain, serviceType, name, port);
        }
    }
     if (name) {
        CFStringToBuffer(name, nameBuf, MAX_DOMAIN_LENGTH);
        if (nameBuf[0] && is_domain_blocked(nameBuf)) {
            CFStringRef dummyDomain = CFSTR("127.0.0.1");
            return orig_CFNetServiceCreate(alloc, dummyDomain, serviceType, name, port);
        }
    }
    return orig_CFNetServiceCreate(alloc, domain, serviceType, name, port);
}

Boolean my_CFNetServiceSetClient(CFNetServiceRef theService,
                                 CFNetServiceClientCallBack clientCB,
                                 CFNetServiceClientContext *clientContext) {
    char domainBuf[MAX_DOMAIN_LENGTH] = {0};
    char nameBuf[MAX_DOMAIN_LENGTH] = {0};
    if (theService) {
        CFStringRef domain = CFNetServiceGetDomain(theService);
        if (domain) {
            CFStringToBuffer(domain, domainBuf, MAX_DOMAIN_LENGTH);
            if (domainBuf[0] && is_domain_blocked(domainBuf)) {
                return false;
            }
        }
        CFStringRef name = CFNetServiceGetName(theService);
        if (name) {
            CFStringToBuffer(name, nameBuf, MAX_DOMAIN_LENGTH);
            if (nameBuf[0] && is_domain_blocked(nameBuf)) {
                return false;
            }
        }
    }
    return orig_CFNetServiceSetClient(theService, clientCB, clientContext);
}

Boolean my_CFNetServiceResolveWithTimeout(CFNetServiceRef theService,
                                          CFTimeInterval timeout,
                                          CFStreamError *error) {
    char domainBuf[MAX_DOMAIN_LENGTH] = {0};
    if (theService) {
        CFStringRef domain = CFNetServiceGetDomain(theService);
        if (domain) {
            CFStringToBuffer(domain, domainBuf, MAX_DOMAIN_LENGTH);
            if (domainBuf[0] && is_domain_blocked(domainBuf)) {
                return true;
            }
        }
    }
    return orig_CFNetServiceResolveWithTimeout(theService, timeout, error);
}

CFReadStreamRef my_CFStreamCreateForHTTPRequest(CFAllocatorRef alloc, CFHTTPMessageRef request) {
    if (request) {
        CFURLRef url = CFHTTPMessageCopyRequestURL(request);
        if (url) {
            CFStringRef host = CFURLCopyHostName(url);
            if (host) {
                char hostBuf[MAX_DOMAIN_LENGTH] = {0};
                CFStringToBuffer(host, hostBuf, MAX_DOMAIN_LENGTH);
                if (hostBuf[0] && is_domain_blocked(hostBuf)) {
                    CFRelease(host);
                    CFRelease(url);
                    return NULL;
                }
                CFRelease(host);
            }
            CFRelease(url);
        }
    }
    return orig_CFStreamCreateForHTTPRequest(alloc, request);
}

CFHTTPMessageRef my_CFHTTPMessageCreateRequest(CFAllocatorRef alloc,
                                               CFStringRef requestMethod,
                                               CFURLRef url,
                                               CFStringRef httpVersion) {
    if (url) {
        CFStringRef host = CFURLCopyHostName(url);
        if (host) {
            char hostBuf[MAX_DOMAIN_LENGTH] = {0};
            CFStringToBuffer(host, hostBuf, MAX_DOMAIN_LENGTH);
            if (hostBuf[0] && is_domain_blocked(hostBuf)) {
                CFRelease(host);
                return NULL;
            }
            CFRelease(host);
        }
    }
    return orig_CFHTTPMessageCreateRequest(alloc, requestMethod, url, httpVersion);
}

id my_NSNetServiceInitWithDomain(id self, SEL _cmd, id domain, id type, id name) {
    char domainBuf[MAX_DOMAIN_LENGTH] = {0};
    char nameBuf[MAX_DOMAIN_LENGTH] = {0};
    if (domain) {
        CFStringToBuffer((CFStringRef)domain, domainBuf, MAX_DOMAIN_LENGTH);
    }
    if (name) {
        CFStringToBuffer((CFStringRef)name, nameBuf, MAX_DOMAIN_LENGTH);
    }
    if ((domainBuf[0] && is_domain_blocked(domainBuf)) ||
        (nameBuf[0] && is_domain_blocked(nameBuf))) {
        return nil;
    }
    return ((id (*)(id, SEL, id, id, id))orig_NSNetServiceInitWithDomain)(self, _cmd, domain, type, name);
}

id my_NSNetServiceInitWithDomainService(id self, SEL _cmd, id domain, id type, id name, int port) {
    char domainBuf[MAX_DOMAIN_LENGTH] = {0};
    char nameBuf[MAX_DOMAIN_LENGTH] = {0};
    if (domain) {
        CFStringToBuffer((CFStringRef)domain, domainBuf, MAX_DOMAIN_LENGTH);
    }
    if (name) {
        CFStringToBuffer((CFStringRef)name, nameBuf, MAX_DOMAIN_LENGTH);
    }
    if ((domainBuf[0] && is_domain_blocked(domainBuf)) ||
        (nameBuf[0] && is_domain_blocked(nameBuf))) {
        return nil;
    }
    return ((id (*)(id, SEL, id, id, id, int))orig_NSNetServiceInitWithDomainService)(self, _cmd, domain, type, name, port);
}

void my_NSNetServiceResolve(id self, SEL _cmd) {
    id domain = [self valueForKey:@"domain"];
    id name = [self valueForKey:@"name"];
    char domainBuf[MAX_DOMAIN_LENGTH] = {0};
    char nameBuf[MAX_DOMAIN_LENGTH] = {0};
    if (domain) {
        CFStringToBuffer((CFStringRef)domain, domainBuf, MAX_DOMAIN_LENGTH);
    }
    if (name) {
        CFStringToBuffer((CFStringRef)name, nameBuf, MAX_DOMAIN_LENGTH);
    }
    if ((domainBuf[0] && is_domain_blocked(domainBuf)) ||
        (nameBuf[0] && is_domain_blocked(nameBuf))) {
        id delegate = [self valueForKey:@"delegate"];
        if (delegate && [delegate respondsToSelector:@selector(netService:didNotResolve:)]) {
            NSDictionary *errorDict = @{@"NSNetServicesErrorCode": @(NSNetServicesNotFoundError),
                                        @"NSNetServicesErrorDomain": @"NSNetServicesErrorDomain"};
            [delegate netService:self didNotResolve:errorDict];
        }
        return;
    }
    ((void (*)(id, SEL))orig_NSNetServiceResolve)(self, _cmd);
}

id my_NSURLSessionDataTaskWithURL(id self, SEL _cmd, NSURL *url) {
    if (is_url_blocked(url)) {
        NSURLSessionDataTask *emptyTask = [self dataTaskWithURL:[NSURL URLWithString:@"about:blank"]];
        return emptyTask;
    }
    return ((id (*)(id, SEL, NSURL *))orig_NSURLSessionDataTaskWithURL)(self, _cmd, url);
}

id my_NSURLSessionDataTaskWithRequest(id self, SEL _cmd, NSURLRequest *request) {
    if (is_url_blocked(request.URL)) {
        NSURLSessionDataTask *emptyTask = [self dataTaskWithURL:[NSURL URLWithString:@"about:blank"]];
        return emptyTask;
    }
    return ((id (*)(id, SEL, NSURLRequest *))orig_NSURLSessionDataTaskWithRequest)(self, _cmd, request);
}

void my_NSURLConnectionSendAsyncRequest(Class self, SEL _cmd, NSURLRequest *request,
                                       NSOperationQueue *queue,
                                       void (^completionHandler)(NSURLResponse*, NSData*, NSError*)) {
    if (!queue) {
        queue = [NSOperationQueue mainQueue];
    }
    if (is_url_blocked(request.URL)) {
        NSError *error = [NSError errorWithDomain:NSURLErrorDomain
                                             code:NSURLErrorCannotConnectToHost
                                         userInfo:@{NSLocalizedDescriptionKey: @"Connection blocked by content filter"}];
        if (completionHandler) {
            [queue addOperationWithBlock:^{
                completionHandler(nil, nil, error);
            }];
        }
        return;
    }
    ((void (*)(Class, SEL, NSURLRequest *, NSOperationQueue *, void (^)(NSURLResponse*, NSData*, NSError*)))orig_NSURLConnectionSendAsynchronousRequest)
        (self, _cmd, request, queue, completionHandler);
}

void my_UIWebViewLoadRequest(id self, SEL _cmd, NSURLRequest *request) {
    if (is_url_blocked(request.URL)) {
        NSString *html = @"<html />";
        [self loadHTMLString:html baseURL:nil];
        return;
    }
    ((void (*)(id, SEL, NSURLRequest *))orig_UIWebViewLoadRequest)(self, _cmd, request);
}

void my_WKWebViewLoadRequest(id self, SEL _cmd, NSURLRequest *request) {
    if (is_url_blocked(request.URL)) {
        NSString *html = @"<html />";
        [self loadHTMLString:html baseURL:nil];
        return;
    }
    ((void (*)(id, SEL, NSURLRequest *))orig_WKWebViewLoadRequest)(self, _cmd, request);
}

static void swizzleMethod(Class class, SEL originalSelector, IMP replacement, IMP *originalMethod) {
    Method method = class_getInstanceMethod(class, originalSelector);
    if (method) {
        *originalMethod = method_setImplementation(method, replacement);
    }
}

static void swizzleClassMethod(Class class, SEL originalSelector, IMP replacement, IMP *originalMethod) {
    Method method = class_getClassMethod(class, originalSelector);
    if (method) {
        *originalMethod = method_setImplementation(method, replacement);
    }
}

static void free_radix_tree(RadixNode *node) {
    if (!node) return;
    for (int i = 0; i < node->childCount; i++) {
        free_radix_tree(node->children[i].child);
    }
    free(node->children);
    free(node);
}

static void initialize_once(void) {
    dns_cache_init();
    build_domain_trie();
}

__attribute__((constructor))
static void adblock_init(void) {
    pthread_once(&init_once, initialize_once);
    struct rebinding rebindings[] = {
        {"getaddrinfo", my_getaddrinfo, (void *)&orig_getaddrinfo},
        {"gethostbyname", my_gethostbyname, (void *)&orig_gethostbyname},
        {"gethostbyname2", my_gethostbyname2, (void *)&orig_gethostbyname2},
        {"connect", my_connect, (void *)&orig_connect},
        {"sendto", my_sendto, (void *)&orig_sendto},
        {"DNSServiceQueryRecord", my_DNSServiceQueryRecord, (void *)&orig_DNSServiceQueryRecord},
        {"CFNetServiceCreate", my_CFNetServiceCreate, (void *)&orig_CFNetServiceCreate},
        {"CFNetServiceSetClient", my_CFNetServiceSetClient, (void *)&orig_CFNetServiceSetClient},
        {"CFNetServiceResolveWithTimeout", my_CFNetServiceResolveWithTimeout, (void *)&orig_CFNetServiceResolveWithTimeout},
        {"CFStreamCreateForHTTPRequest", my_CFStreamCreateForHTTPRequest, (void *)&orig_CFStreamCreateForHTTPRequest},
        {"CFHTTPMessageCreateRequest", my_CFHTTPMessageCreateRequest, (void *)&orig_CFHTTPMessageCreateRequest}
    };
    
    rebind_symbols(rebindings, sizeof(rebindings)/sizeof(rebindings[0]));
    
    Class nsNetServiceClass = objc_getClass("NSNetService");
    if (nsNetServiceClass) {
        swizzleMethod(nsNetServiceClass,
                      sel_registerName("initWithDomain:type:name:"),
                      (IMP)my_NSNetServiceInitWithDomain,
                      &orig_NSNetServiceInitWithDomain);
        
        swizzleMethod(nsNetServiceClass,
                      sel_registerName("initWithDomain:type:name:port:"),
                      (IMP)my_NSNetServiceInitWithDomainService,
                      &orig_NSNetServiceInitWithDomainService);
        
        swizzleMethod(nsNetServiceClass,
                      sel_registerName("resolve"),
                      (IMP)my_NSNetServiceResolve,
                      &orig_NSNetServiceResolve);
    }
    
    Class urlSessionClass = objc_getClass("NSURLSession");
    if (urlSessionClass) {
        swizzleMethod(urlSessionClass,
                     sel_registerName("dataTaskWithURL:"),
                     (IMP)my_NSURLSessionDataTaskWithURL,
                     &orig_NSURLSessionDataTaskWithURL);
        
        swizzleMethod(urlSessionClass,
                     sel_registerName("dataTaskWithRequest:"),
                     (IMP)my_NSURLSessionDataTaskWithRequest,
                     &orig_NSURLSessionDataTaskWithRequest);
    }
    
    Class urlConnectionClass = objc_getClass("NSURLConnection");
    if (urlConnectionClass) {
        swizzleClassMethod(urlConnectionClass,
                          sel_registerName("sendAsynchronousRequest:queue:completionHandler:"),
                          (IMP)my_NSURLConnectionSendAsyncRequest,
                          &orig_NSURLConnectionSendAsynchronousRequest);
    }
    
    Class uiWebViewClass = objc_getClass("UIWebView");
    if (uiWebViewClass) {
        swizzleMethod(uiWebViewClass,
                      sel_registerName("loadRequest:"),
                      (IMP)my_UIWebViewLoadRequest,
                      &orig_UIWebViewLoadRequest);
    }
    
    Class wkWebViewClass = objc_getClass("WKWebView");
    if (wkWebViewClass) {
        swizzleMethod(wkWebViewClass,
                      sel_registerName("loadRequest:"),
                      (IMP)my_WKWebViewLoadRequest,
                      &orig_WKWebViewLoadRequest);
    }
}

__attribute__((destructor))
static void adblock_deinit(void) {
    if (domain_trie_root) {
        free_radix_tree(domain_trie_root);
        domain_trie_root = NULL;
    }
    
    if (dns_cache) {
        for (int i = 0; i < DNS_CACHE_SIZE; i++) {
            dns_cache_entry_t *entry = atomic_load_explicit(&dns_cache[i], memory_order_acquire);
            while (entry) {
                dns_cache_entry_t *next = entry->next;
                free(entry);
                entry = next;
            }
        }
        free(dns_cache);
        dns_cache = NULL;
    }
    
    for (int i = 0; i < CACHE_MUTEX_COUNT; i++) {
        pthread_mutex_destroy(&cache_mutex[i]);
    }
    
    if (lookup_queue) {
        dispatch_release(lookup_queue);
        lookup_queue = NULL;
    }
    
    if (bloom_filter) {
        free(bloom_filter);
        bloom_filter = NULL;
    }
}

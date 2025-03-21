CC = clang
SDK_PATH = $(shell xcrun --sdk iphoneos --show-sdk-path)
CFLAGS = -Wall -Wextra -arch arm64 -O2 -fpic -dynamiclib -isysroot $(SDK_PATH)
LDFLAGS = -ldl -framework Foundation -framework CoreFoundation -framework CFNetwork

TARGET = adblock.dylib
SRCS = adblock.m fishhook.c

PKG_ROOT = build
INSTALL_DIR = $(PKG_ROOT)/Library/MobileSubstrate/DynamicLibraries
DEB_NAME = com.gamesofts.ios.adblock.deb

domain_list.h: domain_list.txt
	@echo "#ifndef DOMAIN_LIST_H" > domain_list.h
	@echo "#define DOMAIN_LIST_H" >> domain_list.h
	@echo "" >> domain_list.h
	@echo "static const char embedded_domain_list[] =" >> domain_list.h
	@awk '{printf "\"%s\\n\"\n", $$0}' domain_list.txt >> domain_list.h
	@echo ";" >> domain_list.h
	@echo "" >> domain_list.h
	@echo "#endif // DOMAIN_LIST_H" >> domain_list.h

$(TARGET): $(SRCS) domain_list.h
	$(CC) $(CFLAGS) -o $(TARGET) $(SRCS) $(LDFLAGS)

deb: $(TARGET)
	@rm -rf $(PKG_ROOT)
	@mkdir -p $(INSTALL_DIR)
	@mkdir -p $(PKG_ROOT)/DEBIAN
	@cp $(TARGET) $(INSTALL_DIR)/
	@printf "Package: com.gamesofts.ios.adblock\nName: AdBlock IOS Plugin\nVersion: 1.0\nArchitecture: arm64\nDescription: Remove Ads for iOS Rootless\nMaintainer: gamesofts <gamesofts@gmail.com>\n" > $(PKG_ROOT)/DEBIAN/control
	@dpkg-deb --root-owner-group -b $(PKG_ROOT) $(DEB_NAME)

# -*- Makefile -*-

# --------------------------------------------------------------------
.PHONY: default linux linux-on-macos macos
.PHONY: docker-appimage appimage-base appimage-on-macos clean

# --------------------------------------------------------------------
default:
	@echo "make [linux|macos]"

linux:
	scripts/build-linux.sh

linux-on-macos:
	docker run -t -i -e "ECBRANCH=$$ECBRANCH" -v "$$PWD:/home/ci/package" easycryptpa/ec-build-box \
	  sh -c '( set -ex; cp -a package package.dev && make -C package.dev linux && cp -a package.dev/_build-linux package )'

macos:
	scripts/build-macos.sh

appimage-base:
	rm -rf _build-linux/appimage && scripts/build-appimage.sh

docker-appimage:
	cd config/appimage-docker && docker build -t easycryptpa/ec-appimage .

appimage: appimage-base
	docker run -t -i -v "$$PWD:/home/ci/package" easycryptpa/ec-appimage \
	  sh -c '( set -ex; ./appimagetool package/_build-linux/appimage/EasyCrypt package/_build-linux/EasyCrypt.AppImage )'

clean:
	rm -rf _build

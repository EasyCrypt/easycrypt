FROM easycryptpa/ec-build-box

MAINTAINER Pierre-Yves Strub <pierre-yves@strub.nu>

ENV DEBIAN_FRONTEND noninteractive

RUN \
  sudo apt-get install -q -y appstream gnupg2 && \
  curl -L -o appimagetool.AppImage \
    "https://github.com/AppImage/AppImageKit/releases/download/continuous/appimagetool-x86_64.AppImage" && \
  chmod +x appimagetool.AppImage && \
  ./appimagetool.AppImage --appimage-extract && \
  rm ./appimagetool.AppImage && \
  ln -s squashfs-root/AppRun appimagetool

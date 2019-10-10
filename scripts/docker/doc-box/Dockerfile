FROM easycryptpa/ec-build-box:latest

RUN \
	sudo apt-get -q -y install \
	  texlive-base \
	  texlive-binaries \
	  texlive-extra-utils \
	  texlive-font-utils \
	  texlive-fonts-extra \
	  texlive-fonts-recommended \
	  texlive-generic-recommended \
	  texlive-latex-base \
	  texlive-latex-extra \
	  texlive-latex-recommended \
	  texlive-science \
	  python3 python3-pip \
	&& pip3 --no-cache-dir install sphinx sphinx-rtd-theme \
	&& sudo apt-get -q -y clean

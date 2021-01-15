FROM debian:sid

MAINTAINER Pierre-Yves Strub <pierre-yves@strub.nu>

ENV TIMESTAMP=202012161041

ENV DEBIAN_FRONTEND noninteractive

RUN \
	apt-get -q -y update && \
	apt-get -q -y dist-upgrade && \
	apt-get -q -y install sudo m4 rsync git curl wget && \
	apt-get -q -y install python3 python3-pip && \
	pip3 install --no-cache-dir pyyaml && \
	apt-get -q -y --no-install-recommends install mccs ocaml-nox opam aspcud && \
	apt-get -q -y clean

COPY sudo-ci /etc/sudoers.d/ci

RUN addgroup --gid 2000 ci
RUN adduser --disabled-password --gecos "CI" --uid 2000 --gid 2000 ci
RUN chmod 440 /etc/sudoers.d/ci

USER    ci
WORKDIR /home/ci

ENV OPAMYES=true OPAMVERBOSE=0 OPAMJOBS=4 OPAMEXTERNALSOLVER=mccs

RUN \
	opam init --disable-sandboxing -a && \
	opam switch create -v easycrypt ocaml-base-compiler.4.07.1 && \
	opam pin add -n easycrypt https://github.com/EasyCrypt/easycrypt.git && \
	opam install depext && opam depext easycrypt && \
	opam clean

RUN \
	opam install --deps-only easycrypt && opam clean

ENV CVC4V=1.7 Z3V=4.8.4 Z3SV=.d6df51951f4c

RUN \
	opam depext alt-ergo && opam install alt-ergo && opam clean

RUN \
	wget -O cvc4 https://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-${CVC4V}-x86_64-linux-opt && \
        chmod +x cvc4 && mv cvc4 ~/.opam/easycrypt/bin/cvc4

RUN \
	wget https://github.com/Z3Prover/z3/releases/download/z3-${Z3V}/z3-${Z3V}${Z3SV}-x64-ubuntu-16.04.zip && \
        unzip -j z3-${Z3V}${Z3SV}-x64-ubuntu-16.04.zip z3-${Z3V}${Z3SV}-x64-ubuntu-16.04/bin/z3 && \
        chmod +x z3 && mv z3 ~/.opam/easycrypt/bin/z3 && \
	rm -rf z3-${Z3V}${Z3SV}-x64-ubuntu-16.04.zip

RUN \
	opam config exec -- why3 config --detect --full-config

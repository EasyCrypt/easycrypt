FROM debian:sid

MAINTAINER Pierre-Yves Strub <pierre-yves@strub.nu>

ENV DEBIAN_FRONTEND noninteractive

RUN \
	apt-get -q -y update && \
	apt-get -q -y dist-upgrade && \
	apt-get -q -y install sudo m4 rsync git curl wget && \
	apt-get -q -y install python python-pip python3 python3-pip && \
	pip  install --no-cache-dir pyyaml && \
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
	opam remote add easycrypt https://github.com/EasyCrypt/opam.git && \
	opam install depext && opam depext easycrypt ec-provers && \
	opam clean

RUN \
	opam install --deps-only easycrypt && opam clean

ENV CVC4V=1.6 Z3V=4.8.4 Z3H=d6df51951f4c

RUN \
	opam install alt-ergo && \
	wget https://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-${CVC4V}-x86_64-linux-opt && \
        wget https://github.com/Z3Prover/z3/releases/download/z3-${Z3V}/z3-${Z3V}.${Z3H}-x64-debian-8.11.zip && \
        unzip -j z3-${Z3V}.${Z3H}-x64-debian-8.11.zip z3-${Z3V}.${Z3H}-x64-debian-8.11/bin/z3 && \
        rm z3-${Z3V}.${Z3H}-x64-debian-8.11.zip && \
        sudo mv z3 /usr/local/bin/z3 && \
	sudo mv cvc4-${CVC4V}-x86_64-linux-opt /usr/local/bin/cvc4 && \
        sudo chmod u+x /usr/local/bin/cvc4 && \
        sudo chmod u+x /usr/local/bin/z3

RUN \
	opam config exec -- why3 config --detect

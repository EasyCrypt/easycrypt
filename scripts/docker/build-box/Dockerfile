FROM debian:sid

MAINTAINER Pierre-Yves Strub <pierre-yves@strub.nu>

ENV DEBIAN_FRONTEND noninteractive

RUN \
	apt-get -q -y update && \
	apt-get -q -y upgrade && \
	apt-get -q -y install m4 rsync git curl wget && \
	apt-get -q -y install python3 python3-pip && \
	pip3 install --no-cache-dir pyyaml && \
	apt-get -q -y --no-install-recommends install mccs ocaml-nox opam aspcud && \
	apt-get -q -y clean

ENV OPAMROOT=/home/root/.opam OPAMROOTISOK=1 OPAMYES=true OPAMVERBOSE=0 OPAMJOBS=4 OPAMEXTERNALSOLVER=mccs

RUN \
	opam init --disable-sandboxing -a && \
	opam switch create -v easycrypt ocaml-base-compiler.4.12.0 && \
	opam pin add -n easycrypt https://github.com/EasyCrypt/easycrypt.git && \
	opam install depext && opam depext easycrypt && \
	opam clean

RUN \
	opam install --deps-only easycrypt && opam clean

ENV ALTERGO=2.4.0 CVC4V=1.8 Z3V=4.8.10 Z3SV= Z3A=ubuntu-18.04

RUN \
	opam pin add -n alt-ergo ${ALTERGO} && \
        opam depext alt-ergo && opam install alt-ergo && opam clean

RUN \
        wget -O cvc4 https://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-${CVC4V}-x86_64-linux-opt && \
        mv cvc4 /usr/local/bin/ && chmod 755 /usr/local/bin/cvc4

RUN \
        wget https://github.com/Z3Prover/z3/releases/download/z3-${Z3V}/z3-${Z3V}${Z3SV}-x64-${Z3A}.zip && \
        unzip -j z3-${Z3V}${Z3SV}-x64-${Z3A}.zip z3-${Z3V}${Z3SV}-x64-${Z3A}/bin/z3 && \
        cp z3 /usr/local/bin/ && chmod 755 /usr/local/bin/z3 && \
	rm -rf z3-${Z3V}${Z3SV}-x64-${Z3A}.zip

RUN \
	opam config exec -- why3 config detect

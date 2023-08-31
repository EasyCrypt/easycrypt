FROM ghcr.io/easycrypt/ec-base-box:latest

MAINTAINER Pierre-Yves Strub <pierre-yves@strub.nu>

ENV DEBIAN_FRONTEND noninteractive

RUN \
	sudo apt-get -q -y install wget curl python3 python3-pip && \
	sudo apt-get -q -y clean && \
	sudo pip3 install --no-cache-dir pyyaml

RUN \
	opam pin add -n easycrypt https://github.com/EasyCrypt/easycrypt.git && \
	opam install depext && opam depext easycrypt && \
	opam install --deps-only easycrypt && \
	opam clean

ENV ALTERGO=2.4.2 CVC4V=1.8 Z3V=4.8.10 Z3SV= Z3A=ubuntu-18.04

RUN \
	opam pin add -n alt-ergo ${ALTERGO} && \
        opam depext alt-ergo && opam install alt-ergo && opam clean

RUN \
        wget -O cvc4 https://github.com/cvc5/cvc5/releases/download/${CVC4V}/cvc4-${CVC4V}-x86_64-linux-opt && \
        sudo mv cvc4 /usr/local/bin/ && sudo chmod 755 /usr/local/bin/cvc4

RUN \
        wget https://github.com/Z3Prover/z3/releases/download/z3-${Z3V}/z3-${Z3V}${Z3SV}-x64-${Z3A}.zip && \
        unzip -j z3-${Z3V}${Z3SV}-x64-${Z3A}.zip z3-${Z3V}${Z3SV}-x64-${Z3A}/bin/z3 && \
        sudo cp z3 /usr/local/bin/ && sudo chmod 755 /usr/local/bin/z3 && \
	rm -rf z3 z3-${Z3V}${Z3SV}-x64-${Z3A}.zip

RUN \
	opam config exec -- why3 config detect

ARG BASE_LAYER=base
ARG BASE_BUILD_LAYER=base-build
ARG BUILD_LAYER=build

# Base environment
FROM debian:stable AS base

LABEL org.opencontainers.image.maintainer="Pierre-Yves Strub <pierre-yves@strub.nu>"

ARG user=charlie

ENV DEBIAN_FRONTEND=noninteractive

RUN \
	apt-get -q -y update && \
	apt-get -q -y upgrade && \
	apt-get -q -y install sudo && \
	apt-get -q -y clean

COPY --chown=root:root --chmod=0400 docker-parts/sudoers /etc/sudoers.d/

RUN \
	useradd -ms /bin/bash -d /home/$user -g root -G sudo -u 1001 $user

RUN \
	apt-get -q -y install opam && \
	apt-get -q -y clean

USER    $user
WORKDIR /home/$user

ENV OPAMYES=true OPAMVERBOSE=0 OPAMJOBS=4

ARG OCAML_VERSION=5.4.0

RUN \
	opam init --disable-sandboxing --compiler=ocaml-base-compiler.${OCAML_VERSION}

# Build environment
FROM ${BASE_LAYER} AS base-build

RUN \
	sudo apt-get -q -y install wget curl python3 python3-pip python3-yaml && \
	sudo apt-get -q -y clean

RUN \
	opam pin add -n easycrypt https://github.com/EasyCrypt/easycrypt.git && \
	opam install --deps-only --confirm-level=unsafe-yes easycrypt && \
	opam clean

ENV PATH="/home/charlie/bin:$PATH"

FROM ${BASE_BUILD_LAYER} AS build

RUN \
	version=2.6.3 && \
  wget -O alt-ergo https://github.com/OCamlPro/alt-ergo/releases/download/v${version}/alt-ergo-v${version}-x86_64-linux-musl && \
  sudo install -m 0755 alt-ergo /usr/local/bin/alt-ergo-${version} && \
  rm -f alt-ergo

RUN \
	version=2.5.4 && \
  wget -O alt-ergo https://github.com/OCamlPro/alt-ergo/releases/download/v${version}/alt-ergo-v${version}-x86_64-linux-musl && \
  sudo install -m 0755 alt-ergo /usr/local/bin/alt-ergo-${version} && \
  rm -f alt-ergo

RUN \
	version=1.8 && \
	wget -O cvc4 https://github.com/CVC4/CVC4-archived/releases/download/${version}/cvc4-${version}-x86_64-linux-opt && \
	sudo install -m 0755 cvc4 /usr/local/bin/cvc4-${version} && \
	rm -f cvc4

RUN \
	version=1.3.4 && \
	wget -O cvc5.zip https://github.com/cvc5/cvc5/releases/download/cvc5-${version}/cvc5-Linux-x86_64-libcxx-static.zip && \
  unzip -j cvc5.zip cvc5-Linux-x86_64-libcxx-static/bin/cvc5 && \
	sudo install -m 0755 cvc5 /usr/local/bin/cvc5-${version} && \
	rm -f cvc5 cvc5.zip

RUN \
	version=1.2.1 && \
	wget -O cvc5.zip https://github.com/cvc5/cvc5/releases/download/cvc5-${version}/cvc5-Linux-x86_64-static.zip && \
  unzip -j cvc5.zip cvc5-Linux-x86_64-static/bin/cvc5 && \
	sudo install -m 0755 cvc5 /usr/local/bin/cvc5-${version} && \
	rm -f cvc5 cvc5.zip

RUN \
	version=1.1.2 && \
	wget -O cvc5.zip https://github.com/cvc5/cvc5/releases/download/cvc5-${version}/cvc5-Linux-static.zip && \
  unzip -j cvc5.zip cvc5-Linux-static/bin/cvc5 && \
	sudo install -m 0755 cvc5 /usr/local/bin/cvc5-${version} && \
	rm -f cvc5 cvc5.zip

RUN \
	version=1.0.9 && \
	wget -O cvc5 https://github.com/cvc5/cvc5/releases/download/cvc5-${version}/cvc5-Linux && \
	sudo install -m 0755 cvc5 /usr/local/bin/cvc5-${version} && \
	rm -f cvc5

RUN \
	version=4.16.0 && glibc=2.39 && \
	wget -O z3.zip https://github.com/Z3Prover/z3/releases/download/z3-${version}/z3-${version}-x64-glibc-${glibc}.zip && \
	unzip -j z3.zip z3-${version}-x64-glibc-${glibc}/bin/z3 && \
	sudo install -m 0755 z3 /usr/local/bin/z3-${version} && \
	rm -f z3 z3.zip

RUN \
	version=4.15.8 && glibc=2.39 && \
	wget -O z3.zip https://github.com/Z3Prover/z3/releases/download/z3-${version}/z3-${version}-x64-glibc-${glibc}.zip && \
	unzip -j z3.zip z3-${version}-x64-glibc-${glibc}/bin/z3 && \
	sudo install -m 0755 z3 /usr/local/bin/z3-${version} && \
	rm -f z3 z3.zip

RUN \
	version=4.14.1 && glibc=2.35 && \
	wget -O z3.zip https://github.com/Z3Prover/z3/releases/download/z3-${version}/z3-${version}-x64-glibc-${glibc}.zip && \
	unzip -j z3.zip z3-${version}-x64-glibc-${glibc}/bin/z3 && \
	sudo install -m 0755 z3 /usr/local/bin/z3-${version} && \
	rm -f z3 z3.zip

RUN \
	version=4.13.4 && glibc=2.35 && \
	wget -O z3.zip https://github.com/Z3Prover/z3/releases/download/z3-${version}/z3-${version}-x64-glibc-${glibc}.zip && \
	unzip -j z3.zip z3-${version}-x64-glibc-${glibc}/bin/z3 && \
	sudo install -m 0755 z3 /usr/local/bin/z3-${version} && \
	rm -f z3 z3.zip

RUN \
	version=4.12.6 && glibc=2.35 && \
	wget -O z3.zip https://github.com/Z3Prover/z3/releases/download/z3-${version}/z3-${version}-x64-glibc-${glibc}.zip && \
	unzip -j z3.zip z3-${version}-x64-glibc-${glibc}/bin/z3 && \
	sudo install -m 0755 z3 /usr/local/bin/z3-${version} && \
	rm -f z3 z3.zip

RUN \
	version=4.8.17 && glibc=2.31 && \
	wget -O z3.zip https://github.com/Z3Prover/z3/releases/download/z3-${version}/z3-${version}-x64-glibc-${glibc}.zip && \
	unzip -j z3.zip z3-${version}-x64-glibc-${glibc}/bin/z3 && \
	sudo install -m 0755 z3 /usr/local/bin/z3-${version} && \
	rm -f z3 z3.zip

RUN \
	opam exec -- why3 config detect

# Test environment
FROM ${BUILD_LAYER} AS test

ARG EC_VERSION=main
ARG EC_REPO=https://github.com/EasyCrypt/easycrypt.git#${EC_VERSION}

RUN \
	opam pin add -n easycrypt ${EC_REPO} && \
	opam install -v easycrypt && \
	rm -rf .opam/packages.dev/*

FROM ubuntu:16.04

MAINTAINER Pierre-Yves Strub <pierre-yves@strub.nu>

ENV DEBIAN_FRONTEND noninteractive

RUN \
	apt-get -q -y update && \
	apt-get -q -y dist-upgrade && \
	apt-get -q -y install sudo m4 rsync git && \
	apt-get -q -y --no-install-recommends install ocaml-nox opam aspcud && \
	apt-get -q -y clean

COPY sudo-ci /etc/sudoers.d/ci

RUN adduser --disabled-password --gecos "CI" ci
RUN chmod 440 /etc/sudoers.d/ci

USER    ci
WORKDIR /home/ci

ENV OPAMYES     true
ENV OPAMVERBOSE 0
ENV OPAMJOBS    2

RUN \
	opam init -a && \
	opam remote add easycrypt https://github.com/EasyCrypt/opam.git && \
	opam install depext && opam depext easycrypt ec-provers && \
	opam pin add easycrypt https://github.com/EasyCrypt/easycrypt.git#aprhl && \
	opam install easycrypt.dev && \
	rm -rf .opam/packages.dev/* && sudo apt-get -q -y clean

RUN opam config exec -- why3 config --detect

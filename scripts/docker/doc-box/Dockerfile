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

RUN \
	apt-get -q -y install texlive-base && \
	apt-get -q -y clean

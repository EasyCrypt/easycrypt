FROM debian:stable

ARG user=charlie

MAINTAINER Pierre-Yves Strub <pierre-yves@strub.nu>

ENV DEBIAN_FRONTEND noninteractive

RUN \
	apt-get -q -y update && \
	apt-get -q -y upgrade && \
	apt-get -q -y install sudo && \
	apt-get -q -y clean

COPY --chown=root:root --chmod=0400 sudoers /etc/sudoers.d/

RUN \
	useradd -ms /bin/bash -d /home/$user -g root -G sudo -u 1001 $user

RUN \
	apt-get -q -y install opam && \
	apt-get -q -y clean

USER    $user
WORKDIR /home/$user

ENV OPAMYES=true OPAMVERBOSE=0 OPAMJOBS=4

RUN \
	opam init --disable-sandboxing

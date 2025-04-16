FROM debian:bookworm

RUN \
	apt-get update && \
	apt-get -y dist-upgrade && \
	apt-get -y autopurge && \
	apt-get -y install \
		curl \
		git \
		locales \
	&& \
	sed -i '/en_US.UTF-8/s/^# //g' /etc/locale.gen && \
	locale-gen && \
	useradd devcontainer --shell /bin/bash --create-home

ENV LANG=en_US.UTF-8
ENV LANGUAGE=en_US:en
ENV LC_ALL=en_US.UTF-8

USER devcontainer
WORKDIR /home/devcontainer

RUN \
	curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y && \
	.elan/bin/lake --version && \
	echo 'export PATH="$HOME/.elan/bin:$PATH"' >> ~/.bashrc

RUN \
	export PATH="$HOME/.elan/bin:$PATH" && \
	lake new example

USER root
RUN apt-get -y install \
	man \
	less \
	vim
USER devcontainer

# check=skip=FromPlatformFlagConstDisallowed

FROM --platform=linux/amd64 debian:bookworm

ARG username="dev"

RUN \
	sed -i '/PS1.*\\\$/s/\\\$/\\n\0/' '/etc/skel/.bashrc' && \
	useradd "${username}" -ms '/bin/bash'

RUN \
	apt-get update && \
	apt-get -y dist-upgrade && \
	apt-get -y autopurge

RUN \
	apt-get -y install locales && \
	sed -i '/en_US.UTF-8/s/^# //g' '/etc/locale.gen' && \
	locale-gen

ENV LANG="en_US.UTF-8"
ENV LANGUAGE="en_US:en"
ENV LC_ALL="en_US.UTF-8"

RUN \
	apt-get -y install \
		curl

USER "${username}"

RUN \
	curl -L 'https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh' |  sh -s -- -y

RUN \
	bash -lc "elan toolchain install "$(curl -s 'https://api.github.com/repos/leanprover/lean4/tags' | sed '/name/!d;/rc/d;s/.*\(v[^"]*\).*/\1/;q')""

USER root

RUN \
	apt-get -y install \
		git \
		gnupg \
		less \
		man \
		openssh-client \
		patch \
		vim

USER "${username}"

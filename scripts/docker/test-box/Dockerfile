FROM easycryptpa/ec-build-box:latest

ARG SOURCE_BRANCH=1.0

RUN \
	opam pin --dev-repo add -n easycrypt https://github.com/EasyCrypt/easycrypt.git#${SOURCE_BRANCH} && \
	opam install -v easycrypt && \
	rm -rf .opam/packages.dev/*

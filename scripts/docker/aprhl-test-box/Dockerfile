FROM easycryptpa/ec-build-box:latest

RUN \
	opam pin add -n easycrypt https://github.com/EasyCrypt/easycrypt.git#aprhl && \
	opam install easycrypt.dev && \
	rm -rf .opam/packages.dev/*

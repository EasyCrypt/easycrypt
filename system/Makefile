#! -*- Makefile -*-

# --------------------------------------------------------------------
.PHONY: all clean

CC       = gcc
CPPFLAGS =
CFLAGS   = -Wall -W -Wno-unused-function -std=gnu99
LDFLAGS  =

# --------------------------------------------------------------------
BIN = callprover

# --------------------------------------------------------------------
all: $(BIN)

$(BIN): $(BIN).o
	$(CC) -o $@ $(LDFLAGS) $^

clean:
	rm -f $(BIN) $(BIN).o

%.o: %.c
	$(CC) -c -o $@ $(CPPFLAGS) $(CFLAGS) $<

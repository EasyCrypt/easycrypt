#! -*- Makefile -*-

# --------------------------------------------------------------------
.PHONY: all clean

CC       = gcc
CPPFLAGS =
CFLAGS   = -Wall -W -Wno-unused-function -std=gnu99
LDFLAGS  =

# --------------------------------------------------------------------
OS  = $(shell uname -o)
BIN = callprover
EXE =

ifeq ($(OS),Cygwin)
CFLAGS  += -municode
LDFLAGS += -municode
EXE      = .exe
endif

# --------------------------------------------------------------------
all: $(BIN)$(EXE)

$(BIN)$(EXE): $(BIN).o
	$(CC) -o $@ $(LDFLAGS) $^

clean:
	rm -f $(BIN)$(EXE) $(BIN).o

%.o: %.c
	$(CC) -c -o $@ $(CPPFLAGS) $(CFLAGS) $<

callprover.o: win32/callprover.c unix/callprover.c

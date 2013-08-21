#! -*- Makefile -*-

# --------------------------------------------------------------------
.PHONY: all clean

CC       = gcc
CPPFLAGS =
CFLAGS   = -Wall -W -Wno-unused-function -std=gnu99
LDFLAGS  =

# --------------------------------------------------------------------
BIN = callprover
EXE =

MACHINE = $(shell $(CC) -dumpmachine)

# Use gcc to check if we are compiling for Cygwin or MinGW-w64.
ifneq (,$(findstring w64,$(MACHINE)))
CFLAGS  += -municode
LDFLAGS += -municode
EXE      = .exe
else
ifneq (,$(findstring cygwin,$(MACHINE)))
EXE      = .exe
endif
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

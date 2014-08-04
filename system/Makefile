#! -*- Makefile -*-

# --------------------------------------------------------------------
.PHONY: all clean

# --------------------------------------------------------------------
BIN      = callprover
CPPFLAGS = 
CFLAGS   = -Wall -W -Wno-unused-function -std=gnu99
LDFLAGS  =

include ../Makefile.system

ifneq (,$(findstring mingw,$(MACHINE)))
CFLAGS  += -municode
LDFLAGS += -municode
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

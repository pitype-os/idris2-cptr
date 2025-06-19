TARGET = libcptr-idris
LIBTARGET = $(TARGET).a
TARGET_VERSION ?= 0.0.1

INSTALLDIR = ../lib

RANLIB ?= ranlib

CC=riscv64-unknown-elf-gcc
LDFLAGS =
CPPFLAGS = -fno-builtin -Wno-int-conversion -Wno-implicit-function-declaration -Wno-pointer-to-int-cast -Wall -Wextra -c -mcmodel=medany
CC_VERSION = $(shell $(CC) --version)

SRCS = $(wildcard *.c)
OBJS = $(SRCS:.c=.o)

all: build

.PHONY: build
build: $(LIBTARGET)

$(LIBTARGET): $(OBJS)
	$(AR) rc $@ $^
	$(RANLIB) $@

.PHONY: clean
clean :
	rm -f $(OBJS) $(TARGET)
	rm -rf $(INSTALLDIR)

.PHONY: install

install:
	mkdir -p $(INSTALLDIR)
	install $(LIBTARGET) $(wildcard *.h) $(INSTALLDIR)

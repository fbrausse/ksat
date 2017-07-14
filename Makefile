DESTDIR ?= /usr/local
INSTALL = install

CXXFLAGS = -O2 -Wall -g
LDFLAGS = -g
override CXX += -std=c++14

LIB_OBJS = ksat.o
OBJS = main.o $(LIB_OBJS)

ksat: override CC=$(CXX)
ksat: $(OBJS)

$(OBJS): %.o: %.cc $(wildcard *.hh *.h) Makefile

libksat.a: $(LIB_OBJS)
	$(AR) rcs $@ $^

install: ksat libksat.a
	mkdir -p $(DESTDIR)/include/ksat && $(INSTALL) -m 0644 common.h ksat.hh $(DESTDIR)/include/ksat
	mkdir -p $(DESTDIR)/lib && $(INSTALL) -m 0644 libksat.a $(DESTDIR)/lib
	mkdir -p $(DESTDIR)/bin && $(INSTALL) -m 0755 ksat $(DESTDIR)/bin

uninstall:
	$(RM) $(DESTDIR)/include/ksat/ksat.hh
	$(RM) $(DESTDIR)/lib/libksat.a
	$(RM) $(DESTDIR)/bin/ksat

clean:
	$(RM) $(OBJS) ksat libksat.a

.PHONY: install uninstall clean

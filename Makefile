CXXFLAGS = -O2 -Wall -g
LDFLAGS = -g
override CXX += -std=c++14

OBJS = main.o ksat.o

ksat: override CC=$(CXX)
ksat: $(OBJS)

$(OBJS): %.o: %.cc $(wildcard *.hh *.h) Makefile

clean:
	$(RM) $(OBJS) ksat

.PHONY: clean

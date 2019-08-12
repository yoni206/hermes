default: bin

include Makefile.config

# The order in the list below should reflect dependencies
MODULES = arith bool congruence instantiation number symbolic \
	parsers/smtlib2 parsers/tptp parsers/dimacs pre proof utils SAT .

PWD     = $(shell pwd)
BASEDIR = $(subst $(empty) $(empty),*,${PWD})
ifneq "$(wildcard ${BASEDIR}/extern/reduce)" ""
  REDARCH := $(shell ${BASEDIR}/extern/reduce/scripts/findhost.sh $$(${BASEDIR}/extern/reduce/config.guess))
  LDFLAGS += -L${BASEDIR}/extern/reduce/generic/libreduce/${REDARCH} -lreduce
  MODULES += nla
  CFLAGS  += -DNLA
  $(shell rm -f ${BASEDIR}/extern/reduce/generic/libreduce/${REDARCH}/libreduce.so)
endif

SUBDIRS = $(MODULES:%=src/%)
INCLUDES= $(SUBDIRS:%=-I %)

CTEMPLATES=$(wildcard src/arith/*-xx.c.tpl)
HTEMPLATES=$(wildcard src/arith/*-xx.h.tpl)
C_HW=$(CTEMPLATES:%-xx.c.tpl=%-hw.c)
C_MP=$(CTEMPLATES:%-xx.c.tpl=%-mp.c)
H_HW=$(HTEMPLATES:%-xx.h.tpl=%-hw.h)
H_MP=$(HTEMPLATES:%-xx.h.tpl=%-mp.h)
GENERATEDR=\
	$(H_HW) $(H_MP) $(C_HW) $(C_MP) \
	src/parsers/smtlib2/smtlex.c \
	src/parsers/smtlib2/smtsyn.c \
	src/parsers/tptp/tptplex.c \
	src/parsers/tptp/tptpsyn.c
GENERATED=$(GENERATEDR) \
	src/parsers/smtlib2/smtsyn.h \
	src/parsers/tptp/tptpsyn.h

CSRC=$(filter-out $(GENERATED),$(foreach SUBDIR,${SUBDIRS},$(wildcard ${SUBDIR}/*.c))) $(filter %.c,$(GENERATED))
OBJS=$(CSRC:%.c=%.o)

OBJS_FIRST =$(GENERATEDR)

ifneq "$(wildcard ${BASEDIR}/extern/gmp)" ""
  LDFLAGS += -L${BASEDIR}/extern/gmp/lib -lgmp
  INCLUDES += -I ${BASEDIR}/extern/gmp/include
  OBJS_FIRST += extern/gmp
endif


.PHONY: extern/gmp
extern/gmp:
	${MAKE} -C ${BASEDIR}/extern/gmp all

%-hw.c: %-xx.c.tpl
	@$(ECHO) "SED $<"
	@sed "s/xx/hw/g;s/XX/HW/g" $< > $@

%-mp.c: %-xx.c.tpl
	@$(ECHO) "SED $<"
	@sed "s/xx/mp/g;s/XX/MP/g" $< > $@

%-hw.h: %-xx.h.tpl
	@$(ECHO) "SED $<"
	@sed "s/xx/hw/g;s/XX/HW/g" $< > $@

%-mp.h: %-xx.h.tpl
	@$(ECHO) "SED $<"
	@sed "s/xx/mp/g;s/XX/MP/g" $< > $@

src/arith/LA-mp.c: $(H_MP)

src/arith/LA-hw.o: src/arith/LA-hw.c
	@$(ECHO) "CC $<"
	@$(CC) $(INCLUDES) $(CPPFLAGS) $(filter-out -Werror, $(CFLAGS)) -o $@ -c $<

src/arith/LA-mp.o: src/arith/LA-mp.c
	@$(ECHO) "CC $<"
	@$(CC) $(INCLUDES) $(CPPFLAGS) $(filter-out -Werror, $(CFLAGS)) -o $@ -c $<

src/parsers/smtlib2/smtsyn.c: YFLAGS += -p yy2
src/parsers/tptp/tptpsyn.c: YFLAGS += -p yy3
src/parsers/smtlib2/smtlex.c: LFLAGS += -P yy2
src/parsers/tptp/tptplex.c: LFLAGS += -P yy3

src/parsers/smtlib2/smtsyn.o: src/parsers/smtlib2/smtsyn.c
	@$(ECHO) "CC $<"
	@$(CC) $(INCLUDES) $(CPPFLAGS) $(filter-out -Werror, $(CFLAGS)) -o $@ -c $<

src/parsers/smtlib2/smtlex.o: src/parsers/smtlib2/smtlex.c src/parsers/smtlib2/smtsyn.c
	@$(ECHO) "CC $<"
	@$(CC) $(INCLUDES) $(CPPFLAGS) $(filter-out -Wall -Wextra -pedantic -Wconversion -Wdeclaration-after-statement -Wmissing-prototypes -Werror, $(CFLAGS)) -o $@ -c $<

src/parsers/tptp/tptpsyn.o: src/parsers/tptp/tptpsyn.c
	@$(ECHO) "CC $<"
	@$(CC) $(INCLUDES) $(CPPFLAGS) $(filter-out -Werror, $(CFLAGS)) -o $@ -c $<

src/parsers/tptp/tptplex.o: src/parsers/tptp/tptplex.c src/parsers/tptp/tptpsyn.c
	@$(ECHO) "CC $<"
	@$(CC) $(INCLUDES) $(CPPFLAGS) $(filter-out -Wall -Wextra -pedantic -Wconversion -Wdeclaration-after-statement -Wmissing-prototypes -Werror, $(CFLAGS)) -o $@ -c $<

src/SAT/veriT-SAT.o: src/SAT/veriT-SAT.c
	@$(ECHO) "CC $<"
	@$(CC) $(INCLUDES) $(CPPFLAGS) -DINSIDE_VERIT $(CFLAGS) -o $@ -c $<

src/SAT/veriT-SAT-standalone.o: src/SAT/veriT-SAT.c
	@$(ECHO) "CC $<"
	@$(CC) $(filter-out -DPROOF, $(CPPFLAGS)) $(CFLAGS) -o $@ -c $<

.SECONDARY: $(C_HW) $(C_MP) $(H_HW) $(H_MP)

all: bin

bin: veriT veriT-SAT

$(OBJS): | $(OBJS_FIRST)

veriT: $(OBJS)
	@$(ECHO_N) "Linking veriT..."
	@$(CC) $(CFLAGS) $(OBJS) $(LDFLAGS) -o veriT
	@$(ECHO) "done"

veriT-SAT: src/SAT/veriT-SAT-standalone.o src/veriT-SAT/main.o
	@$(ECHO_N) "Linking veriT-SAT..."
	@$(CC) $(CFLAGS) $^ $(LDFLAGS) -o veriT-SAT
	@$(ECHO) "done"

install: bin
	$(INSTALL) veriT $(PREFIX_BIN)
	$(INSTALL) veriT-SAT $(PREFIX_BIN)

clean veryclean::
	@$(ECHO) "Cleaning up..."
	@$(RM) *~ veriT veriT-SAT src/SAT/veriT-SAT-standalone.o src/veriT-SAT/main.o
	@$(RM) $(OBJS) $(GENERATED)

ifeq ($(DOXYGEN),doxygen)
doc::
	$(MKDIR) doc/user
	$(DOXYGEN) doc/Doxyfile.libveriT.user
	$(DOXYGEN) doc/Doxyfile.veriT.user
	$(MKDIR) doc/dev
	$(DOXYGEN) doc/Doxyfile.dev

.PHONY: doc
endif

ifeq ($(ETAGS),etags)
tags:
	for F in `find src -name "*.[ch]" -print`; do $(ETAGS) -a $$F; done
.PHONY: tags
endif

ifeq ($(CTAGS), ctags)
ctags:
	ctags -Re

.PHONY: ctags
endif

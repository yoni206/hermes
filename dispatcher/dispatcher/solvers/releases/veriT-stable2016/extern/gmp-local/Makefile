DIR=gmp-6.0.0
SOURCES:=gmp-6.0.0a.tar.bz2
LIB=lib

CONFIGUREFLAGS=--prefix=$(PWD)/extern/gmp --disable-shared
ifdef TARGET
CONFIGUREFLAGS += --host=$(TARGET)
endif

.DEFAULT_GOAL := all

$(SOURCES):
	wget "http://ftpmirror.gnu.org/gmp/$(SOURCES)"

$(DIR): $(SOURCES)
	tar xjf $(SOURCES)

$(LIB): $(DIR)
	cd $(DIR) && (unset CFLAGS && ./configure $(CONFIGUREFLAGS)) && make && make install

all: $(LIB)

veryclean:
	cd $(DIR) && make clean

clean:

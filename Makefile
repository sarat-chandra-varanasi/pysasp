# pysasp Makefile - Main
# Version 20192511

export PLEXE_EXE = pysasp

SRCDIR = src

.PHONY: all
all: PLEXE_EXE

.PHONY: PLEXE_EXE
PLEXE_EXE:
	$(MAKE) -C $(SRCDIR) -w
	mv -f $(SRCDIR)/$(PLEXE_EXE) .

.PHONY: clean
clean:
	cd $(SRCDIR) && make -w clean
	rm -f core gmon.out $(PLEXE_EXE) $(PLEXE_EXE).exe

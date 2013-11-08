SRC= Axioms.v Common.v EqT.v Vector.v Word.v Data.v Finite.v  Sumn.v  Reify.v Base.v Simulation.v Combinators.v Netlist.v Count.v Delay.v Tagger.v Lifting.v
EX= Doors.v MoreDoors.v Muxer.v DC.v Ripple.v  FIFO.v  Register.v 

EXAMPLES=$(addprefix Examples/,$(EX))
OBJ= $(SRC:.v=.vo) $(EXAMPLES:.v=.vo)
COQBIN=
COQC=$(COQBIN)coqc -I . -I Examples
COQDEP:=$(COQBIN)coqdep -c
COQLIB:=$(shell $(COQBIN)coqtop -where | sed -e 's/\\/\\\\/g')
COQDEBUG=
COQFLAGS=

all: $(OBJ)  .depend 

test: .depend Examples/Interpretations.vo

world : all test

%.vo : %.v 
	$(COQC) $(COQDEBUG) $(COQFLAGS) $*

clean:
	rm -f $(OBJ) *.glob *~
	- rm -rf html
	- rm -f .depend

%.v.d: %.v
	$(COQDEP) -slash $(COQLIBS) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

.PHONY : .depend

.depend:
	$(COQDEP) -I . -I Examples $(SRC) $(EXAMPLES) Examples/Interpretations.v > .depend 2> /dev/null

-include $(VFILES:.v=.v.d)
.SECONDARY: $(VFILES:.v=.v.d)

# .depend contains dependencies for .mli files
-include .depend
.SECONDARY: .depend


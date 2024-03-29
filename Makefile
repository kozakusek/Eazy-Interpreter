## File generated by the BNF Converter (bnfc 2.9.4).

# Makefile for building the parser and test program.

GHC        = ghc
GHC_OPTS   = -o interpreter
HAPPY      = happy
HAPPY_OPTS = --array --info --ghc --coerce
ALEX       = alex
ALEX_OPTS  = --ghc
#BNFC_PATH  = /home/students/inf/PUBLIC/MRJP/bin/bnfc 
BNFC_PATH  = ./dev/bnfc

# List of goals not corresponding to file names.

.PHONY : all clean distclean

# Default goal.

all : Main

# Rules for building the parser.

Eazy/Abs.hs Eazy/Lex.x Eazy/Par.y Eazy/Print.hs Eazy/Test.hs : eazy.cf
	${BNFC_PATH} --haskell -d --functor eazy.cf

%.hs : %.y
	${HAPPY} ${HAPPY_OPTS} $<

%.hs : %.x
	${ALEX} ${ALEX_OPTS} $<

Main: Eazy/Abs.hs Eazy/Lex.hs Eazy/Par.hs Eazy/Print.hs TypeChecker.hs Prologue.hs Interpreter.hs Main.hs
	${GHC} ${GHC_OPTS} Main.hs

# Rules for cleaning generated files.

clean :
	-rm -f Eazy/*.hi Eazy/*.o Eazy/*.log Eazy/*.aux Eazy/*.dvi *.hi *.o interpreter

distclean : clean
	-rm -f Eazy/Abs.hs Eazy/Abs.hs.bak Eazy/ComposOp.hs Eazy/ComposOp.hs.bak Eazy/Doc.txt Eazy/Doc.txt.bak Eazy/ErrM.hs Eazy/ErrM.hs.bak Eazy/Layout.hs Eazy/Layout.hs.bak Eazy/Lex.x Eazy/Lex.x.bak Eazy/Par.y Eazy/Par.y.bak Eazy/Print.hs Eazy/Print.hs.bak Eazy/Skel.hs Eazy/Skel.hs.bak Eazy/Test.hs Eazy/Test.hs.bak Eazy/XML.hs Eazy/XML.hs.bak Eazy/AST.agda Eazy/AST.agda.bak Eazy/Parser.agda Eazy/Parser.agda.bak Eazy/IOLib.agda Eazy/IOLib.agda.bak Eazy/Main.agda Eazy/Main.agda.bak Eazy/eazy.dtd Eazy/eazy.dtd.bak Eazy/Test Eazy/Lex.hs Eazy/Par.hs Eazy/Par.info Eazy/ParData.hs
	-rmdir -p Eazy/

# EOF

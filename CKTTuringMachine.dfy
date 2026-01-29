
include "objects.dfy"
include "turing_machine.dfy"
include "certificate.dfy"
const CircuitSymbols := {NonBlankSymbol("AND"), NonBlankSymbol("OR"), NonBlankSymbol("NOT"), 
                         NonBlankSymbol("1"), NonBlankSymbol("POSITION"), NonBlankSymbol("VARIABLE")}
const AnySymbol := CircuitSymbols+{NonBlankSymbol("TRUE"),NonBlankSymbol("FALSE")}
const NonVariableSymbols:=CircuitSymbols-{NonBlankSymbol("VARIABLE")}
const NonPosSymbols := CircuitSymbols-{NonBlankSymbol("POSITION")}
const AnyNonPosSymbols := CircuitSymbols-{NonBlankSymbol("POSITION")}+{NonBlankSymbol("TRUE"),NonBlankSymbol("FALSE")}
const NonOneSymbols := CircuitSymbols-{NonBlankSymbol("1")}
const Gtransitions1 := (map sym | sym in CircuitSymbols ::
    Key(NormalState("g"),sym) := Action(NormalState("g"), sym, Right))
const GTransitions:=Gtransitions1+ map
[ 
    Key(NormalState("g"),NonBlankSymbol("CERT")):= Action(NormalState("gf"),NonBlankSymbol("CERT"),Right),
    Key(NormalState("g"),NonBlankSymbol("TRUE")):= Action(FinalState("WTF",Reject),NonBlankSymbol("TRUE"),Right),
    Key(NormalState("g"),NonBlankSymbol("FALSE")):= Action(FinalState("WTF",Reject),NonBlankSymbol("FALSE"),Right)
]
const GFtransitions1 := map sym | (sym in CircuitSymbols+{NonBlankSymbol("CERT")})::
    Key(NormalState("gf"),sym) := Action(FinalState("WTF",Reject),NonBlankSymbol("FALSE"),Right)
const GFtransitions2 := map sym | (sym in {NonBlankSymbol("TRUE"),NonBlankSymbol("FALSE")})::
    Key(NormalState("gf"),sym) := Action(NormalState("gf"),sym,Right)
const GFTransitions := GFtransitions1+GFtransitions2+map[
     Key(NormalState("gf"),Blank) := Action(NormalState("gfi"),Blank,Left)
]
const GFITransitions:= map[
    Key(NormalState("gfi"),NonBlankSymbol("CERT")):= Action(NormalState("s"),Blank,Left),
    Key(NormalState("gfi"),NonBlankSymbol("TRUE")):= Action(NormalState("gfT"),Blank,Left),
    Key(NormalState("gfi"),NonBlankSymbol("FALSE")):= Action(NormalState("gfF"),Blank,Left)
]
const GFBOOLtransitions1:= map sym,s | sym in CircuitSymbols-{NonBlankSymbol("VARIABLE")} 
&& s in {NormalState("gfT"),NormalState("gfF"),NormalState("gi")} ::
    Key(s,sym):= Action(s,sym,Left)
const GFBOOLtransitions2:= map 
    [
        Key(NormalState("gfF"),NonBlankSymbol("VARIABLE")):= Action(NormalState("gi"),NonBlankSymbol("FALSE"),Right),
        Key(NormalState("gfT"),NonBlankSymbol("VARIABLE")):= Action(NormalState("gi"),NonBlankSymbol("TRUE"),Right),
        Key(NormalState("gfF"),Blank):= Action(NormalState("g"),Blank,Right),
        Key(NormalState("gfT"),Blank):= Action(NormalState("g"),Blank,Right),
        Key(NormalState("gi"),Blank):= Action(NormalState("g"),Blank,Right)
    ]
const GFBOOLtransitions3:=map sym,s |  sym in NonVariableSymbols && s in {NormalState("gff"),NormalState("gft")} ::
    Key(s,sym):= Action(FinalState("WTF",Reject),NonBlankSymbol("FALSE"),Right)
const GFBOOLtransitions4:=map sym,s |  sym in {NonBlankSymbol("FALSE"),NonBlankSymbol("TRUE")} && s in {NormalState("gff"),NormalState("gft")} ::
    Key(s,sym):= Action(s,sym,Right)
const GFBOOLtransitions5:=map [
    Key(NormalState("gff"),NonBlankSymbol("VARIABLE")):= Action(NormalState("g"),NonBlankSymbol("FALSE"),Right),
    Key(NormalState("gft"),NonBlankSymbol("VARIABLE")):= Action(NormalState("g"),NonBlankSymbol("TRUE"),Right)
]
const GFBOOLTransitions:=GFBOOLtransitions1+GFBOOLtransitions2+GFBOOLtransitions3+GFBOOLtransitions4+GFBOOLtransitions5

const GuessPhaseTransitions:= GFBOOLTransitions+GFTransitions+GTransitions+GFITransitions

const Stransitions1 := map sym | sym in AnyNonPosSymbols-{NonBlankSymbol("VARIABLE")} :: 
    Key(NormalState("s"),sym) :=  Action(NormalState("s"),sym,Left)
const Stransitions2 := map [
    Key(NormalState("s"),Blank) := Action(NormalState("si"),Blank,Right),
    Key(NormalState("s"),NonBlankSymbol("VARIABLE")) := Action(FinalState("WTF",Reject),NonBlankSymbol("FALSE"),Right),
    Key(NormalState("s"),NonBlankSymbol("CERT")) := Action(FinalState("WTF",Reject),NonBlankSymbol("FALSE"),Right)
]


const SItransitions1 := map sym | sym in CircuitSymbols+{NonBlankSymbol("1")} ::
    Key(NormalState("si"),sym) := Action(FinalState("WTF",Reject),NonBlankSymbol("FALSE"),Right)
const SItransitions2 := map [
    Key(NormalState("si"),NonBlankSymbol("TRUE")) :=Action(NormalState("sit"),Blank,Right),
    Key(NormalState("si"),NonBlankSymbol("FALSE")) :=Action(NormalState("sif"),Blank,Right) 
]

const SITtransitions1 := map s | s in {NormalState("sit"),NormalState("sitn")}::
    Key(s,NonBlankSymbol("POSITION")) := Action(NormalState("sitnr"),NonBlankSymbol("POSITION"),Right)
const SIFtransitions1 := map s | s in {NormalState("sif"),NormalState("sifn")}::
    Key(s,NonBlankSymbol("POSITION")) := Action(NormalState("sifnr"),NonBlankSymbol("POSITION"),Right)
const SIBOOltransitions2:= map symbol,s | symbol in {NonBlankSymbol("TRUE"),NonBlankSymbol("FALSE")} && s in {NormalState("sit"),NormalState("sif"),NormalState("sifn"),NormalState("sitn")}::
    Key(s,symbol):=Action(s,symbol,Right)
const SIBOOltransitions3:= map [
    Key(NormalState("sif"),NonBlankSymbol("AND")) := Action(NormalState("siANDf"),NonBlankSymbol("AND"),Left),
    Key(NormalState("sit"),NonBlankSymbol("AND")) := Action(NormalState("siANDt"),NonBlankSymbol("AND"),Left),


    Key(NormalState("siANDt"),NonBlankSymbol("TRUE")) := Action(NormalState("siANDtt"),Blank,Right),
    Key(NormalState("siANDf"),NonBlankSymbol("TRUE")) := Action(NormalState("siANDf"),Blank,Right),


    Key(NormalState("siANDf"),NonBlankSymbol("FALSE")) := Action(NormalState("siANDf"),Blank,Right),
     Key(NormalState("siANDt"),NonBlankSymbol("FALSE")) := Action(NormalState("siANDf"),Blank,Right),


    Key(NormalState("siANDtt"),NonBlankSymbol("AND")) := Action(NormalState("sin"),NonBlankSymbol("TRUE"),Right),
    Key(NormalState("siANDf"),NonBlankSymbol("AND")) := Action(NormalState("sin"),NonBlankSymbol("FALSE"),Right),


    Key(NormalState("sif"),NonBlankSymbol("OR")) := Action(NormalState("siORf"),NonBlankSymbol("OR"),Left),
    Key(NormalState("sit"),NonBlankSymbol("OR")) := Action(NormalState("siORt"),NonBlankSymbol("OR"),Left),

    Key(NormalState("siORt"),NonBlankSymbol("TRUE")) := Action(NormalState("siORt"),Blank,Right),
    Key(NormalState("siORt"),NonBlankSymbol("FALSE")) := Action(NormalState("siORt"),Blank,Right),

    Key(NormalState("siORf"),NonBlankSymbol("FALSE")) := Action(NormalState("siORff"),Blank,Right),
    Key(NormalState("siORf"),NonBlankSymbol("TRUE")) := Action(NormalState("siORt"),Blank,Right),

    Key(NormalState("siORff"),NonBlankSymbol("OR")) := Action(NormalState("sin"),NonBlankSymbol("FALSE"),Right),
    Key(NormalState("siORt"),NonBlankSymbol("OR")) := Action(NormalState("sin"),NonBlankSymbol("TRUE"),Right),

    Key(NormalState("sif"),NonBlankSymbol("NOT")) := Action(NormalState("sin"),NonBlankSymbol("TRUE"),Right),
    Key(NormalState("sit"),NonBlankSymbol("NOT")) := Action(NormalState("sin"),NonBlankSymbol("FALSE"),Right),

    Key(NormalState("sin"),Blank) := Action(NormalState("s"),Blank,Left),
    Key(NormalState("sit"),Blank) := Action(FinalState("true",Accept),Blank,Left),
    Key(NormalState("sif"),Blank) := Action(FinalState("false",Reject),Blank,Left)
]
const SIBoolTransitionsN := map sym | sym in AnySymbol ::
    Key(NormalState("syn"),sym) := Action (NormalState("syn"),sym,Right)

const SIFNRtransitions1 := map s | s in {NormalState("sifnr")} ::
    Key(s,NonBlankSymbol("1")) :=Action(NormalState("sifnrig"),NonBlankSymbol("empty"),Right) 
    
const SIFNRtransitions2 := map s,sym | s in {NormalState("sifnr")} && sym in NonOneSymbols ::    
    Key(s,sym) :=Action(NormalState("sifnri"),sym,Left)

const SITNRtransitions1 := map s | s in {NormalState("sitnr")} ::
    Key(s,NonBlankSymbol("1")) :=Action(NormalState("sitnrig"),NonBlankSymbol("empty"),Right) 
    
const SITNRtransitions2 := map s,sym | s in {NormalState("sitnr")} && sym in NonOneSymbols ::    
    Key(s,sym) :=Action(NormalState("sitnri"),sym,Left)

const SiBoolNrtransitions3 := map s,sym | s in {NormalState("sitnr"),NormalState("sifnr")} && sym in {NonBlankSymbol("TRUE"),NonBlankSymbol("FALSE")} ::
     Key(s,sym) :=Action(s,sym,Right)
const SiBoolNrtransitions4 := map s | s in {NormalState("sitnr"),NormalState("sifnr")} ::
     Key(s,Blank) :=Action(NormalState("s"),Blank,Left)

const SIBoolNrItransitions1:= map [
    Key(NormalState("sitnri"),NonBlankSymbol("Position")) := Action(NormalState("sitn"),NonBlankSymbol("TRUE"),Right),
    Key(NormalState("sifnri"),NonBlankSymbol("Position")) := Action(NormalState("sifn"),NonBlankSymbol("FALSE"),Right)
]
const AnyNonOneSymbol:= AnySymbol-{NonBlankSymbol("1")}
const SITNRIgtransitions1 :=map sym | sym in AnyNonOneSymbol ::
    Key(NormalState("sitnrig"),sym) := Action(NormalState("sitn"),sym,Right)
const SIFNRIgtransitions1 :=map sym | sym in AnyNonOneSymbol ::
    Key(NormalState("sifnrig"),sym) := Action(NormalState("sifn"),sym,Right)
const SITNRIgtransitions2 :=map sym,s | sym==NonBlankSymbol("1") && s==NormalState("sitnrig") ::
    Key(s,sym) := Action(s,sym,Right)
const SIFNRIgtransitions2 :=map sym,s | sym==NonBlankSymbol("1") && s==NormalState("sifnrig") ::
    Key(s,sym) := Action(s,sym,Right)
const SITNgtransitions1 :=map sym | sym in AnyNonPosSymbols ::
    Key(NormalState("sitn"),sym) := Action(NormalState("sitn"),sym,Right)
const SIFNtransitions1 :=map sym | sym in AnyNonOneSymbol ::
    Key(NormalState("sifn"),sym) := Action(NormalState("sifn"),sym,Right)
const SIBoolNtransitions3:= map s | s in {NormalState("sifn"),NormalState("sitn")} ::
    Key(s,Blank) := Action(NormalState("s"),Blank,Left)

const SINTransitions := SITNRIgtransitions1+SIFNRIgtransitions1+SITNRIgtransitions2+SIFNRIgtransitions2+SITNgtransitions1+SIFNtransitions1+SIBoolNtransitions3
const SIBoolNrTransitions := SIFNRtransitions1+SIFNRtransitions2+SITNRtransitions1+SITNRtransitions2+SiBoolNrtransitions3+SiBoolNrtransitions4
const SIBoolTransitions:= SITtransitions1+SIFtransitions1+SIBOOltransitions2+SIBOOltransitions3+SIBoolTransitionsN
const STransitions:= Stransitions1+Stransitions2
const SITransitions:= SItransitions1+SItransitions2


const EmptyTransitions := map sym,s | sym==NonBlankSymbol("empty") 
    && s in {NormalState("s"), NormalState("si"), NormalState("sit"), NormalState("sif"), NormalState("sitn"), 
    NormalState("sitnr"), NormalState("sifn"), NormalState("sifnr"), NormalState("siANDf"), NormalState("siANDt"), 
    NormalState("siANDtt"), NormalState("siANDf"), NormalState("sitANDt"), NormalState("sitANDf"), NormalState("sin"), 
    NormalState("siORf"), NormalState("siORt"), NormalState("siORff"), NormalState("sitORt"), NormalState("sitORf"), 
    NormalState("syn"), NormalState("sifnrig"), NormalState("sifnri"), NormalState("sitnrig"), NormalState("sitnri")} ::
    Key(s,sym):=Action(s,sym,Right)

const SolvePhaseTransitions :=SINTransitions+ SIBoolNrTransitions+SIBoolTransitions+STransitions+SITransitions+EmptyTransitions
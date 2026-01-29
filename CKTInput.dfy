include "objects.dfy"
include "turing_machine.dfy"
include "certificate.dfy"
const CKTSymbolStrings:=["AND","OR","NOT","VARIABLE","1","POSITION"]
const CKTInputSymbols:={NonBlankSymbol("AND"),NonBlankSymbol("OR"),NonBlankSymbol("NOT"),NonBlankSymbol("VARIABLE"),NonBlankSymbol("1"),NonBlankSymbol("POSITION"),NonBlankSymbol("TRUE"),NonBlankSymbol("FALSE"),NonBlankSymbol("CERT")}
const CKTAddTapeSymbols:={Blank,NonBlankSymbol("Empty")}
function getPosition(input:seq<string>,nr:nat) : nat 
    requires nr<=|input|
    decreases |input|-nr
{
    if nr==|input| || input[nr]!="1" then
        0
    else 
        1+getPosition(input,nr+1)
}
predicate isInputGoodForCKT(input:seq<string>)
{
    forall pos:nat::pos<|input| ==> input[pos] in CKTSymbolStrings
}
predicate isInputCKT (input:seq<string>)
    requires isInputGoodForCKT(input)
{
    forall pos:nat::pos<|input| ==> isInputCKT'(input,pos)
}
predicate theLastTwoGatesArePOS (input:seq<string>, pos:nat)
    requires pos<|input|
{
    if input[pos]=="1"
    then
        match getPOZ(input,pos)
            case Some(nr) => getPOZ(input,nr)!=None
            case None => false
    else
        false
}

predicate theLastGateIsPOS(input:seq<string>,pos:nat)
    requires pos<|input|
{
    if input[pos]=="1"
    then 
        getPOZ(input,pos)!=None
    else 
        false
}
function getCanonicalPOS(input:seq<string>,pos:nat) : nat
    requires pos<|input|
    requires input[pos]!="1"
{
    getCanonicalPOS'(input,0,pos)
}
function getCanonicalPOS'(input:seq<string>,initPos:nat,pos:nat) :nat
    requires pos<|input|
    requires initPos<=pos
    requires input[pos]!="1"
    decreases pos-initPos
{
    if initPos==pos then 
        0
    else 
        if (input[initPos]!="1" && input[initPos]!="POSITION") then 
            1+getCanonicalPOS'(input,initPos+1,pos)
        else 
            getCanonicalPOS'(input,initPos+1,pos)

}
function getPOZ(input:seq<string>,pos:int) : Option<nat>
    requires -1<=pos<|input|
    ensures match getPOZ(input,pos)
                case Some(nr) => nr<=pos
                case None => true
    decreases pos
{
    if pos==-1 || (input[pos]!="1" && input[pos]!="POSITION") then
        None
    else
        if input[pos]=="POSITION" then
            Some(pos) 
        else
            getPOZ(input,pos-1)
}
function getCanonicalElement(input:seq<string>,pos:nat):Option<string>    
    ensures  match getCanonicalElement(input,pos)
                    case Some(str) => str!="1" && str!="POSITION"
                    case None => true 
{
    getCanonicalElement'(input,0,0,pos)
}
function getCanonicalElement'(input:seq<string>,initPos:nat,gateCnt:nat,canonPos:nat):Option<string>
    requires initPos<=|input|
    decreases |input|-initPos
    ensures  match getCanonicalElement'(input,initPos,gateCnt,canonPos)
                    case Some(str) => str!="1" && str!="POSITION"
                    case None => true 
{
    if initPos==|input| then
        None
    else 
        if input[initPos]=="1"  || input[initPos]=="POSITION" then
            getCanonicalElement'(input,initPos+1,gateCnt,canonPos)
        else
            if gateCnt==canonPos then 
                Some(input[initPos])
            else 
                getCanonicalElement'(input,initPos+1,gateCnt+1,canonPos)

}
predicate isInputCKT' (input:seq<string>, pos:nat) // nu mai ai nume custom pentru variabile
    requires pos<|input|
    requires isInputGoodForCKT(input)
{
    match input[pos]
        case "AND" => 2<pos<|input| && theLastTwoGatesArePOS (input, pos-1)
        case "OR" => 2<pos<|input| && theLastTwoGatesArePOS (input, pos-1)
        case "NOT" => 1<pos<|input| && theLastGateIsPOS (input, pos-1)
        case "VARIABLE" => true
        case "POSITION" => getPosition(input,pos)<getCanonicalPOS(input,pos) && (match getCanonicalElement(input,getCanonicalPOS(input,pos))
                                                                                    case Some(str) => str!="POSITION"
                                                                                    case None => false )
        case "1" => getPOZ(input,pos)!=None
}
function nthVariableInput (input:seq<string>, pos:nat) : nat
    requires pos<|input|
    requires input[pos]=="VARIABLE"
{
    nthVariableInput'(input,0,pos)
}
function nthVariableInput'(input:seq<string>,initPos:nat, pos:nat) :nat 
    requires initPos<=pos
    requires pos<|input|
    requires input[pos]=="VARIABLE"
    ensures initPos<pos && input[initPos]=="VARIABLE" ==> nthVariableInput'(input,initPos,pos)==nthVariableInput'(input,initPos+1,pos)+1
    ensures initPos<pos ==> nthVariableInput'(input,initPos,pos)>=nthVariableInput'(input,initPos+1,pos)
    decreases pos-initPos
{
    if initPos==pos then 
        0
    else
        if input[initPos]=="VARIABLE" then
           nthVariableInput'(input,initPos+1,pos)+1
        else
            nthVariableInput'(input,initPos+1,pos)
}
lemma nthVariableInputIsUnique (input:seq<string>, pos1:nat,pos2:nat)
    requires pos1<pos2<|input|
    requires input[pos1]=="VARIABLE" && input[pos2]=="VARIABLE"
    ensures nthVariableInput(input,pos1)<nthVariableInput(input,pos2)
{
    assert nthVariableInput(input,pos1)==nthVariableInput'(input,0,pos1);
    assert nthVariableInput(input,pos2)==nthVariableInput'(input,0,pos2);
    assert nthVariableInput'(input,pos1,pos2)>nthVariableInput'(input,pos1,pos1);
    if pos1>0 {
        for k:=pos1-1 downto 0
            invariant nthVariableInput'(input,k,pos2)>nthVariableInput'(input,k,pos1)
        {
        }
    }
    assert nthVariableInput'(input,0,pos2)>nthVariableInput'(input,0,pos1);
}
predicate isCertificateValidForInput (input:seq<string>,k:seq<string>)
    requires isCertificateCorrectForm(k)
{
    forall pos:nat:: pos<|input| && input[pos]=="VARIABLE" ==> nthVariableInput(input,pos)<|k|
}
ghost predicate isLanguageCKT(l:Language)
{
    forall input:seq<string> :: (input in l) <==> isInputGoodForCKT(input) && isInputCKT(input) 
}
lemma CKTInputSymbolsIsgoodForLanguage(l:Language)
    requires isLanguageCKT(l)
    ensures forall input:seq<string> :: (input in l) ==> 
    isInputValid(input,CKTInputSymbols)
{
    var input:| input in l;
    assert isInputGoodForCKT(input);
    assert forall pos:nat::pos<|input| ==> input[pos] in ["AND","OR","NOT","VARIABLE","1","POSITION"];
    assert forall pos:nat::pos<|input| ==> (NonBlankSymbol(input[pos]) in CKTInputSymbols);
    assert forall str:string :: (str in input) ==> (exists pos:nat::pos<|input| && input[pos]==str);
    assert forall str:string :: (str in input) ==> (exists pos:nat::pos<|input| && input[pos]==str && (NonBlankSymbol(input[pos]) in CKTInputSymbols));
    assert forall str:string :: (str in input) ==> (NonBlankSymbol(str) in CKTInputSymbols);
}
lemma CKTInputSymbolsIsgoodForCertificate(k:certificate)
    requires isCertificateCorrectForm(k)
    ensures isInputValid(k,CKTInputSymbols)
{
    assert forall str:string::(str in k) ==> str in ["TRUE","FALSE"];
}
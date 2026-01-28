include "objects.dfy"
include "turing_machine.dfy"
include "certificate.dfy"
predicate isInputCKT (input:seq<string>)
{
    forall pos:nat::pos<|input| ==> isInputCKT'(input,pos)
}
predicate isStringAGate(str:string)
{
    str=="AND" || str=="OR" || str=="NOT"
}
predicate isInputGoodForCKT(input:seq<string>)
{
    forall pos:nat::pos<|input| ==> isStringGoodForCKT(input[pos],pos)
}
predicate isStringGoodForCKT(str:string,pos:nat)
{
    if !isStringAValidNumber(str) then (str in ["AND","OR","NOT","VARIABLE"])
    else
        stringToNat(str)<pos
}
predicate isAGoodVariableInput(x:string)
{
    !(x in ReservedWords) && !isStringAValidNumber(x)
}
predicate isStringAValidPos(input:seq<string>, pos:nat)
    requires pos<|input|
    requires isStringAValidNumber(input[pos])
{
    0<=stringToNat(input[pos])<pos && !isStringAValidNumber(input[stringToNat(input[pos])])
}
predicate isInputCKT' (input:seq<string>, pos:nat) // nu mai ai nume custom pentru variabile
    requires pos<|input|
{
    match input[pos]
        case "AND" => 2<pos<|input| && isStringAValidNumber(input[pos-1]) && isStringAValidNumber(input[pos-2]) 
        case "OR" => 2<pos<|input| && isStringAValidNumber(input[pos-1]) && isStringAValidNumber(input[pos-2])
        case "NOT" => 1<pos<|input|&& isStringAValidNumber(input[pos-1]) && isStringAValidPos(input, pos-1) 
        case "VARIABLE" => true
        case x => isStringAValidNumber(x) && isStringAValidPos(input,pos)
}
lemma aCKTInputIsGood (input:seq<string>)
    requires isInputCKT(input)
    ensures isInputGoodForCKT(input)
{
     for pos:=0 to |input|
        invariant 0 <= pos <= |input|
        invariant forall k :: 0 <= k < pos ==> isStringGoodForCKT(input[k],k)
    {
        if pos<|input| 
        {
            assert isInputCKT'(input,pos);
            if isStringAValidNumber(input[pos])
            {

            }
        }
    }    
    assert forall pos:nat::pos<|input| ==> isStringGoodForCKT(input[pos],pos);
}
 lemma ValidInputExtension(input: seq<string>, ext: seq<string>)
    requires isInputCKT(input)
    requires forall k :: |input| <= k <|input|+ |ext| ==> isInputCKT'(input + ext, k)
    ensures isInputCKT(input + ext)
{
    var combined := input+ ext;
    assert forall i :: 0 <= i < |input| ==> combined[i] == input[i];
    assert forall i :: 0 <= i < |input| ==> isInputCKT'(input, i);
    assert forall i :: 0 <= i < |input| && isInputCKT'(input,i)==> isInputCKT'(combined, i);
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
    forall input:seq<string> :: (input in l) <==> isInputCKT(input) 
}
ghost predicate isInputSymbolsValidForLanguage(l:Language,inputS:InputSymbols)
{
    forall input:seq<string>::  input in l <==> 
                                exists c:seq<string>,k:certificate :: isCertificateCorrectForm(k) && isInputValid(input+k,inputS)
}
ghost predicate inputSymbolsForCKT (inputS:InputSymbols,l:Language)
    requires isLanguageCKT(l)
{
    isInputSymbolsValidForLanguage(l,inputS)
}
ghost predicate AdditionalTapeSymbolsForCKT(inputS:InputSymbols,l:Language,addTapeS:AdditionalTapeSymbols)
    requires isLanguageCKT(l)
    requires isInputSymbolsValidForLanguage(l,inputS)
{
    isTapeSymbolsValid(inputS,addTapeS)
}

predicate isCKTInputString(s: string)
{
  isStringAValidNumber(s)
  || s == "AND"
  || s == "OR"
  || s == "NOT"
  || s == "VARIABLE"
  || s == "TRUE"
  || s == "FALSE"
}
predicate isCKTInputSymbol(sym: Symbol)
{
  match sym
    case NonBlankSymbol(s) => isCKTInputString(s)
    case Blank => false
}


include "objects.dfy"
include "turing_machine.dfy"
include "certificate.dfy"
predicate isInputCKT (input:seq<string>)
{
    forall pos:nat::pos<|input| ==> isInputCKT'(input,pos)
}
predicate isStringAGate(str:string)
{
    str=="AND" || str=="OR" || str=="NOR"
}
predicate isAGoodPozInput(nr:string,poz:nat)
    requires isStringAValidNumber(nr)
{
    poz-1-stringToNat(nr)>=0
}
predicate isAGoodVariableInput(x:string)
{
    !(x in ReservedWords) && !isStringAValidNumber(x)
}
predicate isStringAValidPos(input:seq<string>, pos:nat)
    requires pos<|input|
    requires isStringAValidNumber(input[pos])
{
    pos-1-stringToNat(input[pos])>=0 && !isStringAValidNumber(input[pos-1-stringToNat(input[pos])])
}
predicate isInputCKT' (input:seq<string>, pos:nat)
    requires pos<|input|
{
    match input[pos]
        case "AND" => 2<pos<|input| && isStringAValidNumber(input[pos-1]) && isStringAValidPos(input, pos-1) && isStringAValidNumber(input[pos-2]) && isStringAValidPos(input, pos-2)
        case "OR" => 2<pos<|input| && isStringAValidNumber(input[pos-1]) && isStringAValidPos(input, pos-1) && isStringAValidNumber(input[pos-2]) && isStringAValidPos(input, pos-2)
        case "NOT" => 1<pos<|input|&& isStringAValidNumber(input[pos-1]) && isStringAValidPos(input, pos-1) 
        case x => if isStringAValidNumber(x) then isStringAValidPos(input, pos)
                    else !(x in ReservedWords)
}

 lemma Lemma_ValidInputExtension(input: seq<string>, ext: seq<string>)
    requires isInputCKT(input)
    requires forall k :: |input| <= k <|input|+ |ext| ==> isInputCKT'(input + ext, k)
    ensures isInputCKT(input + ext)
{
    var combined := input+ ext;
    assert forall i :: 0 <= i < |input| ==> combined[i] == input[i];
    assert forall i :: 0 <= i < |input| ==> isInputCKT'(input, i);
    assert forall i :: 0 <= i < |input| && isInputCKT'(input,i)==> isInputCKT'(combined, i);
}
predicate isCertificateValidForInput (input:seq<string>,k:seq<string>)
    requires isCertificateCorrectForm(k)
{
    forall pos:nat:: pos<|input| ==> if !(input[pos] in ReservedWords) && !isStringAValidNumber(input[pos]) then (input[pos] in k) else true
}
ghost predicate isLanguageCKT(l:Language)
{
    forall input:seq<string> :: (input in l) <==> exists pos:nat:: 1<=pos<|input|-3 
                                            && isInputCKT(input) 
}
ghost predicate isInputSymbolsValidForLanguage(l:Language,inputS:InputSymbols)
{
    forall input:seq<string>::  input in l <==> 
                                exists c:seq<string> :: isInputValid(input+c,inputS)
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
// lemma isCKTNP (l:Language)
// requires isLanguageCKT(l)
// ensures isLanguageNPTIME2(l)
// {

// }
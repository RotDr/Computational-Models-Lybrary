include "turing_machine.dfy"
datatype gate = AND (i1:nat,i2:nat)| OR(i1:nat,i2:nat) | NOT(i:nat) | VARIABLE(x:string) 
type circuit=seq<gate>
type certificate=seq<string>
function natToString(n: nat): string {
    match n
    case 0 => "0" case 1 => "1" case 2 => "2" case 3 => "3" case 4 => "4"
    case 5 => "5" case 6 => "6" case 7 => "7" case 8 => "8" case 9 => "9"
    case _ => natToString(n / 10) + natToString(n % 10)
  }
function stringToNat(s:string): Option<nat> {
    if |s|!=0 then
        stringToNat'(s,0)
    else
        None
}
function stringToNat'(s:string,pos:nat):Option<nat>
    requires pos<=|s|
    decreases |s|-pos
{
    if pos==|s| then
         Some(0)
    else
        if s[pos] >='0' && s[pos]<='9' then
            match stringToNat'(s,pos+1)
                case Some(n) => Some(n*10+(s[pos] as int - '0' as int))    
                case None => None
        else
            None
}

predicate isCircuitValid (c:circuit)
{
     forall pos:nat :: 0<=pos<|c| ==>  match c[pos]
        case AND (i1,i2) => i1>=0 && i1>=0 && i1<pos && i2<pos
        case OR (i1,i2) => i1>=0 && i1>=0 && i1<pos && i2<pos
        case NOT (i) => i>=0 && i<pos
        case VARIABLE (_) => true 
}

function gateToString (g:gate) : string
{
    match g
        case AND (i1,i2) => "AND: "+natToString(i1)+" "+natToString(i2)    
        case OR (i1,i2) => "OR: "+natToString(i1)+" "+natToString(i2)
        case NOT (i) => "Not: "+natToString(i)
        case VARIABLE (x) => x
}
function circuitToInput (c:circuit) : seq<string>
{
    circuitToInput'(c,0)
}
function circuitToInput' (c:circuit,pos:nat) :seq<string>
    requires |c|>=pos
    decreases |c|-pos
{
    if pos==|c| then []
    else [gateToString(c[pos])] + circuitToInput'(c,pos+1)
}
function inputToCircuit (input:seq<string>) : circuit
{
    input
}
predicate isCertificateValid (c:circuit,k:certificate)
{
    forall pos:nat:: pos<|c| ==> (
            match c[pos] 
                case VARIABLE(x) => exists poz:nat :: poz<|k| && (
                    k[poz]==x+" : "+"1" || k[poz]==x+" : "+"0") 
                case _ => true
        )
}
function getValueFromCertificate (v:string,k:certificate):Option<bool>
    ensures getValueFromCertificate(v,k)!=None <==>exists poz:nat :: poz<|k| && (
                    k[poz]==v+" : "+"1" || k[poz]==v+" : "+"0")

{
    getValueFromCertificate'(v,k,0)
}
function getValueFromCertificate'(v:string,k:certificate,pos:nat):Option<bool>
    requires pos<=|k|
    decreases |k|-pos
    ensures getValueFromCertificate'(v,k,pos)!=None <==>exists poz:nat :: poz<|k| && (
                    k[poz]==v+" : "+"1" || k[poz]==v+" : "+"0")
    requires forall poz:nat ::poz<pos ==> ( k[poz]!=v+" : "+"1" && k[poz]!=v+" : "+"0")
    ensures forall poz:nat ::poz<pos ==> ( k[poz]!=v+" : "+"1" && k[poz]!=v+" : "+"0")
{
    if pos==|k| then None
    else
        if k[pos]==v+" : "+"1" then 
            Some(true)
        else
            if  k[pos]==v+" : "+"0" then
            Some(false)
        else 
            getValueFromCertificate'(v,k,pos+1)
}
predicate solveCircuit(c:circuit,k:certificate)
    requires isCircuitValid(c)
    requires isCertificateValid(c,k)
    requires |c|>=1
{
    solveCircuit'(c,k,|c|-1)
}
predicate solveCircuit'(c:circuit,k:certificate,pos:nat)
    requires isCircuitValid(c)
    requires isCertificateValid(c,k)
    requires |c|>=1
    requires pos<|c|
    decreases pos
{

    match c[pos]
        case AND (i1,i2) =>     solveCircuit'(c,k,i1) && solveCircuit'(c,k,i2)
        case OR (i1,i2) =>      solveCircuit'(c,k,i1) || solveCircuit'(c,k,i2)
        case NOT (i) =>         solveCircuit'(c,k,i)
        case VARIABLE (x) =>     match getValueFromCertificate(x,k)
                                        case Some(st) => st
}
ghost function generateCKTSATLanguage ():Language 
{
    generateCKTSATLanguage'({})
}
predicate checkSatisfaction(c:circuit)
    requires isCircuitValid(c)
{
    exists k:certificate :: isCertificateValid(c,k) && solveCircuit(c,k)
}
ghost predicate isThatActuallyTheCKTSATLanguage (l:Language) 
{
    forall input:seq<string> :: (input in l) ==> 
}
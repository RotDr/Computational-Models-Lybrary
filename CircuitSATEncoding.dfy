include "turing_machine.dfy"
datatype circuitCell = AND | OR | NOT | VARIABLE(x:string) | POZ(i:nat)
type circuit=seq<circuitCell>
type certificate=seq<string>
type stringNat = s: string |
    |s| > 0 && (|s| > 1 ==> s[0] != '0') &&
    forall i | 0 <= i < |s| :: s[i] in "0123456789"
    witness "1"
predicate isStringAValidNumber (s:string)
{
    |s| > 0 && (|s| > 1 ==> s[0] != '0') &&
    forall i | 0 <= i < |s| :: s[i] in "0123456789"
}
  function natToString(n: nat): string
    ensures isStringAValidNumber(natToString(n))
   {
    match n
    case 0 => "0" case 1 => "1" case 2 => "2" case 3 => "3" case 4 => "4"
    case 5 => "5" case 6 => "6" case 7 => "7" case 8 => "8" case 9 => "9"
    case _ => natToString(n / 10) + natToString(n % 10)
  }

  function stringToNat(s: string): nat
    decreases |s|
    requires isStringAValidNumber(s)
  {
    if |s| == 1 then
      match s[0]
      case '0' => 0 case '1' => 1 case '2' => 2 case '3' => 3 case '4' => 4
      case '5' => 5 case '6' => 6 case '7' => 7 case '8' => 8 case '9' => 9
    else
      stringToNat(s[..|s|-1])*10 + stringToNat(s[|s|-1..|s|])
  }
  lemma natToStringThenStringToNatIdem(n: nat)
    ensures stringToNat(natToString(n)) == n
  { 
  }
  lemma stringToNatThenNatToStringIdem(n: string)
    requires isStringAValidNumber(n)
    ensures natToString(stringToNat(n)) == n
  { 
  }
predicate isCircuitCellAPoz (e:circuitCell)
{
     match e
        case POZ(nr) => true
        case _ => false 
}
predicate isCircuitCellAValidPoz (e:circuitCell,poz:nat,c:circuit)
    requires poz<|c|
{
    match e
        case POZ(nr) => (
            if 0<=nr<poz-1 then 
                !isCircuitCellAPoz(c[nr]) 
            else 
                false)
        case _ => false 
}
predicate isCktValid(c:circuit)
{
    forall pos:nat :: 0<=pos<|c| ==>  match c[pos]
        case AND => pos<|c|-2 && isCircuitCellAValidPoz(c[pos+1],pos,c) && isCircuitCellAValidPoz(c[pos+2],pos,c)
        case OR => pos<|c|-2 && isCircuitCellAValidPoz(c[pos+1],pos,c) && isCircuitCellAValidPoz(c[pos+2],pos,c)
        case NOT => pos<|c|-1 && isCircuitCellAValidPoz(c[pos+1],pos,c) 
        case VARIABLE (_) => true 
        case POZ(nr) => ( pos>0 && 0<nr<pos-1 && pos-nr-1>=0)
}
predicate isCircuitValid (c:circuit)
{
    forall pos:nat :: 0<=pos<|c| ==> isCircuitValid'(c,pos)
}
predicate isCircuitValid'(c:circuit, pos:nat)
    requires pos<|c|
{
    match c[pos]
            case AND => pos<|c|-2 && isCircuitCellAValidPoz(c[pos+1],pos,c) && isCircuitCellAValidPoz(c[pos+2],pos,c)
            case OR => pos<|c|-2 && isCircuitCellAValidPoz(c[pos+1],pos,c) && isCircuitCellAValidPoz(c[pos+2],pos,c)
            case NOT => pos<|c|-1 && isCircuitCellAValidPoz(c[pos+1],pos,c) 
            case VARIABLE (x) => x!="true" && x!="false" 
            case POZ(nr) => ( pos>0 && 0<nr<pos-1 && pos-nr-1>=0 && !isCircuitCellAPoz(c[nr]))
}
ghost function circuitToInput (c:circuit) : seq<string>
    requires isCircuitValid(c)
{
    circuitToInput'(c,0)
}
ghost function circuitToInput' (c:circuit,poz:nat) :seq<string>
    requires poz<=|c|
    requires  isCircuitValid(c)
    decreases |c|-poz
{
    if poz==|c| then []
    else 
        match c[poz]
            case AND => ["AND"]+circuitToInput'(c,poz+1)
            case OR => ["OR"]+circuitToInput'(c,poz+1)
            case NOT => ["NOT"]+circuitToInput'(c,poz+1)
            case VARIABLE(x) => [x]+circuitToInput'(c,poz+1)
            case POZ(nr) =>
            assert isCircuitValid'(c, poz);
            assert 0<nr<poz-1;
            assert poz-nr-1>0;
            [natToString(poz-nr-1)]+circuitToInput'(c,poz+1)

}
function inputToCircuit (input:seq<string>) : Option<circuit>
 {
     inputToCircuit'(input,0)
 }
function inputToCircuit' (input:seq<string>,pos:nat) : Option<circuit>
    requires pos<=|input|
    decreases |input|-pos
{
    if pos==|input| then Some([])
    else
        match stringToCircuitCell(input[pos],pos)
            case Some(g) =>(
                match inputToCircuit'(input,pos+1)
                    case Some(l) => Some([g]+l)
                    case None => None
            )
            case None=> None
}
function stringToCircuitCell(s:string,pos:nat) : Option<circuitCell>
{
    if s=="AND" then Some(AND) 
    else
    if s=="OR" then Some(OR) 
    else 
    if s=="NOT" then Some(NOT)
    else
    if isStringAValidNumber(s) then 
        if (pos-stringToNat(s)-1<=0) then
            None
        else 
            Some(POZ(pos-stringToNat(s)-1))

    else
        Some(VARIABLE(s))
}
predicate isCertificateCorrectForm (k:certificate)
{
    (|k|>0 && |k|%2==0) && forall pos:nat:: pos<|k| ==> (if pos%2==0 then 
    (k[pos]!="true" && k[pos]!="false") 
    else (k[pos]=="true" || k[pos]=="false"))     
}
predicate isCertificateValid (c:circuit,k:certificate)
    requires isCertificateCorrectForm(k)
{
     forall pos:nat:: pos<|c| ==> variableHasValue(c,k,pos)
 }
 predicate variableHasValue(c:circuit,k:certificate,pos:nat)
    requires pos<|c|
 {
    match c[pos] 
                 case VARIABLE(x) => exists poz:nat :: (poz<|k|-1 && (
                     k[poz]==x && (k[poz+1]=="true" && k[poz+1]=="false"))) 
                 case _ => true
 }
function getValueFromCertificate (v:string,k:certificate):Option<bool>
     requires v!="false" && v!="true"
     requires isCertificateCorrectForm (k)

{
    getValueFromCertificate'(v,k,0)
}
function getValueFromCertificate'(v:string,k:certificate,pos:nat):Option<bool>
    requires pos<|k|
    requires v!="false" && v!="true"
    decreases |k|-pos
    ensures getValueFromCertificate'(v,k,pos)!=None <==>exists poz:nat :: (poz<|k|-1 && (
                    k[poz]==v && (k[poz+1]=="true" || k[poz+1]=="false")))
    requires forall poz:nat ::poz<pos ==> k[poz]!=v
    ensures forall poz:nat ::poz<pos ==>  k[poz]!=v
    requires isCertificateCorrectForm(k)

{
    if pos==|k|-1 then None
    else
        if k[pos]==v then(
            assert  v!="false" && v!="true";
            assert k[pos]!="false" && k[pos]!="true";
            assert k[pos+1]=="true" || k[pos+1]=="false";
            if k[pos+1]=="true" then 
                Some(true)
            else
                Some(false)
            )
        else
            getValueFromCertificate'(v,k,pos+1)
}
predicate solveCircuit(c:circuit,k:certificate)
    requires isCircuitValid(c)
    requires isCertificateCorrectForm(k)
    requires isCertificateValid(c,k)
    requires |c|>=1
{
    solveCircuit'(c,k,|c|-1)
}
function getNumberFromPoz(e:circuitCell) : nat
    requires isCircuitCellAPoz(e)
{
    match e
        case POZ(nr) => nr
}
predicate solveCircuit'(c:circuit,k:certificate,pos:nat)
    requires isCircuitValid(c)
    requires isCertificateCorrectForm(k)
    requires isCertificateValid(c,k)
    requires |c|>=1
    requires pos<|c|
    decreases pos
{

    match c[pos]
        case AND =>  
            assert  isCircuitValid'(c, pos);    
            solveCircuit'(c,k,getNumberFromPoz(c[pos+1])) && solveCircuit'(c,k,getNumberFromPoz(c[pos+2]))
        case OR  =>
            assert  isCircuitValid'(c, pos);      
        solveCircuit'(c,k,getNumberFromPoz(c[pos+1])) || solveCircuit'(c,k,getNumberFromPoz(c[pos+2]))
        case NOT  =>
            assert  isCircuitValid'(c, pos);         
        !solveCircuit'(c,k,getNumberFromPoz(c[pos+1]))
        case VARIABLE (x) =>( assert isCircuitValid'(c,pos);     
            match getValueFromCertificate(x,k)
                                        case Some(st) => st
                                        case None => false )
        case POZ(nr)=>
            assert  isCircuitValid'(c, pos);
            solveCircuit'(c,k,nr)
}
ghost predicate checkSatisfaction(c:circuit)
    requires isCircuitValid(c)
{
    exists k:certificate :: isCertificateCorrectForm(k) && isCertificateValid(c,k) && |c|>=1 && solveCircuit(c,k)
}
ghost predicate isThatActuallyTheCKTSATLanguage (l:Language) 
{
    (forall input:seq<string> :: (input in l) ==> ( match inputToCircuit(input)
                                                       case Some(c)=>isCircuitValid(c) && checkSatisfaction(c)
                                                       case None=> false))
    &&
    (forall c:circuit :: isCircuitValid(c) && checkSatisfaction(c) ==>
    (circuitToInput(c) in l))
}
predicate areTwoCircuitsTheSame (c1:circuit,c2:circuit)
    ensures areTwoCircuitsTheSame (c1,c2) ==> |c1|==|c2| &&
{
    |c1|==|c2| && forall pos:nat::pos<|c1| ==> c1[pos]==c2[pos]
}
lemma circuitAndInput()
    ensures forall c:circuit:: isCircuitValid(c) ==> (match inputToCircuit(circuitToInput(c))
                                                        case None => false
                                                        case Some(c2)=> areTwoCircuitsTheSame(c,c2) )
{

}
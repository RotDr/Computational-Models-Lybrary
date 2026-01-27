include "objects.dfy"
include "Certificate.dfy"
predicate isCircuitCellAPoz (e:circuitCell)
{
     match e
        case POZ(nr) => true
        case _ => false 
}
predicate isCircuitCellAVariable(e:circuitCell)
{
    match e 
        case VARIABLE(_) => true
        case _ => false
}
predicate isAGoodPoz (e:circuitCell,poz:nat)
    requires isCircuitCellAPoz(e)
{
    match e
        case POZ(nr) => (
            0<=nr<=poz-1)
}
predicate isAGoodVariableCircuit(e:circuitCell)
    requires isCircuitCellAVariable(e)
{
    match e 
        case VARIABLE(x) => !isStringAValidNumber(x) && !(x in ReservedWords)
}
predicate isCircuitGood(c:circuit)
{
    forall poz:nat::poz<|c| ==> isCircuitGood'(c[poz],poz)
}
predicate isCircuitGood'(c:circuitCell,poz:nat)

{
    if isCircuitCellAPoz(c) then
        isAGoodPoz(c,poz)
    else
        if isCircuitCellAVariable(c) then 
            isAGoodVariableCircuit(c)
        else true 
}
predicate isCircuitValid (c:circuit)
{
    forall pos:nat :: 0<=pos<|c| ==> isCircuitValid'(c,pos)
}
predicate isCircuitValid'(c:circuit, pos:nat)
    requires pos<|c|
{
    match c[pos]
            case AND => 2<pos<|c| && isCircuitCellAPoz(c[pos-1]) && isCircuitCellAPoz(c[pos-2])
            case OR => 2<pos<|c|  && isCircuitCellAPoz(c[pos-1]) && isCircuitCellAPoz(c[pos-2])
            case NOT => 1<pos<|c| && isCircuitCellAPoz(c[pos-1]) 
            case VARIABLE (x) => isAGoodVariableCircuit(c[pos])
            case POZ(nr) => isAGoodPoz(c[pos],pos) && !isCircuitCellAPoz(c[nr])
}
// predicate isThatPOZValid(c:circuit,pos:nat)
//     requires pos<|c|
// {
//     match c[pos]
//          case POZ(nr) =>  pos>0 && 0<nr<pos-1 && pos-nr-1>=0 && !isCircuitCellAPoz(c[nr])
//          case _=>true
// }

predicate isCertificateValid (c:circuit,k:certificate)
    requires isCertificateCorrectForm(k)
    requires isCircuitValid(c)
{
     forall pos:nat:: pos<|c| ==> match c[pos]
                                    case VARIABLE(x) => 
                                    assert isCircuitValid'(c,pos);
                                    assert !(x in ReservedWords);
                                    findValue(k,x)!=None
                                    case _ => true
 }
 lemma Lemma_ValidCircuitExtension(c: circuit, ext: seq<circuitCell>)
    requires isCircuitValid(c)
    requires forall k :: |c| <= k <|c|+ |ext| ==> isCircuitValid'(c + ext, k)
    ensures isCircuitValid(c + ext)
{
    var combined := c + ext;

    assert forall i :: 0 <= i < |c| ==> combined[i] == c[i];
    assert forall i :: 0 <= i < |c| ==> isCircuitValid'(c, i);
    assert forall i :: 0 <= i < |c| && isCircuitValid'(c,i)==> isCircuitValid'(combined, i);
    assert isCircuitValid(combined);
}
 predicate variableHasValue(c:circuit,k:certificate,pos:nat)
    requires pos<|c|
 {
    match c[pos] 
                 case VARIABLE(x) => exists poz:nat :: (1<poz<|k| && (
                     k[poz]==x && (k[poz-1]=="TRUE" && k[poz-1]=="FALSE"))) 
                 case _ => true
 }
function getValueFromCertificate (v:string,k:certificate):Option<bool>
     requires v!="FALSE" && v!="TRUE"
     requires isCertificateCorrectForm (k)

{
    getValueFromCertificate'(v,k,0)
}
function getValueFromCertificate'(v:string,k:certificate,pos:nat):Option<bool>
    requires pos<=|k|
    requires v!="FALSE" && v!="TRUE"
    decreases |k|-pos
    ensures getValueFromCertificate'(v,k,pos)!=None <==>exists poz:nat :: (0<poz<|k| && (
                    k[poz]==v && (k[poz-1]=="TRUE" || k[poz-1]=="FALSE")))
    requires forall poz:nat ::poz<pos ==> k[poz]!=v
    ensures forall poz:nat ::poz<pos ==>  k[poz]!=v
    requires isCertificateCorrectForm(k)

{
    if pos==|k| then None
    else
        if k[pos]==v then(
            assert  v!="FALSE" && v!="TRUE";
            assert k[pos]!="TRUE" && k[pos]!="FALSE";
            assert k[pos-1]=="TRUE" || k[pos-1]=="FALSE";
            if k[pos-1]=="TRUE" then 
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
predicate solveCircuit'(c:circuit,k:certificate,pos:nat)
    requires isCircuitValid(c)
    requires |k|>=1 && |k|%2==0
    requires isCertificateCorrectForm(k)
    requires isCertificateValid(c,k)
    requires |c|>=1
    requires pos<|c|
    decreases pos
{

    match c[pos]
        case AND =>  
            assert  isCircuitValid'(c, pos);
            solveCircuit'(c,k,pos-1) && solveCircuit'(c,k,pos-2)
        case OR  =>
            assert  isCircuitValid'(c, pos);
            solveCircuit'(c,k,pos-1) || solveCircuit'(c,k,pos-2)
        case NOT  =>
            assert  isCircuitValid'(c, pos);        
        !solveCircuit'(c,k,pos-1)
        case VARIABLE (x) =>( assert isCircuitValid'(c,pos);     
            match findValue(k,x)
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
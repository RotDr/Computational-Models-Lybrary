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
            0<=nr<poz)
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
        true 
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
            case VARIABLE (x) => true   //( forall poz:nat:: poz<|c| && isCircuitCellAVariable(c[poz]) && poz!=pos 
                                                //==> match c[poz] 
                                                //    case VARIABLE(y) => x!=y)
            case POZ(nr) => isAGoodPoz(c[pos],pos) && !isCircuitCellAPoz(c[nr])
}
lemma aValidCircuitIsGood(c:circuit)
 requires isCircuitValid(c)
    ensures forall pos:nat::pos<|c| && isCircuitCellAPoz(c[pos]) ==> isAGoodPoz(c[pos],pos)
{
    forall pos:nat | pos<|c|
        ensures pos<|c| && isCircuitCellAPoz(c[pos]) ==> isAGoodPoz(c[pos],pos)
    {
        aValidCircuitIsGood'(c,pos);
    }
}
lemma aValidCircuitIsGood' (c:circuit,pos:nat)
    requires isCircuitValid(c)
    ensures pos<|c| && isCircuitCellAPoz(c[pos]) ==> isAGoodPoz(c[pos],pos)
{
    if pos>=|c|
    {

    }
    else
    {
        assert isCircuitValid'(c,pos);
        if isCircuitCellAPoz(c[pos])
        {
            assert isAGoodPoz(c[pos],pos);
        }
    }
}
predicate isThatPOZValid(c:circuit,pos:nat)
    requires pos<|c|
{
    match c[pos]
         case POZ(nr) =>  pos>0 && 0<nr<pos-1 && pos-nr-1>=0 && !isCircuitCellAPoz(c[nr])
         case _=>true
}
predicate areTwoCircuitsTheSame (c1:circuit,c2:circuit)
{
    |c1|==|c2| && forall pos:nat::pos<|c1| ==> c1[pos]==c2[pos]
}
function nthVariableCircuit (c:circuit, pos:nat) : nat
    requires pos<|c|
    requires isCircuitCellAVariable(c[pos])
{
    nthVariableCircuit'(c,0,pos)
}
function nthVariableCircuit'(c:circuit,initPos:nat,pos:nat) :nat 
    requires initPos<=pos
    requires pos<|c|
    requires isCircuitCellAVariable(c[pos])
    ensures initPos<pos && isCircuitCellAVariable(c[initPos]) ==> nthVariableCircuit'(c,initPos,pos)==nthVariableCircuit'(c,initPos+1,pos)+1
    ensures initPos<pos ==> nthVariableCircuit'(c,initPos,pos)>=nthVariableCircuit'(c,initPos+1,pos)
    decreases pos-initPos
{
    if initPos==pos then 
        0
    else
        if isCircuitCellAVariable(c[initPos]) then
            nthVariableCircuit'(c,initPos+1,pos)+1
        else
            nthVariableCircuit'(c,initPos+1,pos)
}
lemma nthVariableCircuitIsUnique (c:circuit, pos1:nat,pos2:nat)
    requires pos1<pos2<|c|
    requires isCircuitCellAVariable(c[pos1]) && isCircuitCellAVariable(c[pos2])
    ensures nthVariableCircuit(c,pos1)<nthVariableCircuit(c,pos2)
{
    assert nthVariableCircuit(c,pos1)==nthVariableCircuit'(c,0,pos1);
    assert nthVariableCircuit(c,pos2)==nthVariableCircuit'(c,0,pos2);
    assert nthVariableCircuit'(c,pos1,pos2)>nthVariableCircuit'(c,pos1,pos1);
    if pos1>0 {
        for k:=pos1-1 downto 0
            invariant nthVariableCircuit'(c,k,pos2)>nthVariableCircuit'(c,k,pos1)
        {
        }
    }
    assert nthVariableCircuit'(c,0,pos2)>nthVariableCircuit'(c,0,pos1);
}

predicate isCertificateValidForCircuit (c:circuit,k:certificate)
    requires isCertificateCorrectForm(k)
    requires isCircuitValid(c)
{
    forall pos:nat:: pos<|c| && isCircuitCellAVariable(c[pos]) ==> nthVariableCircuit(c,pos)<|k|
}
function getValueFromCertificate(c:circuit,pos:nat,k:certificate) : bool
    requires isCertificateCorrectForm(k)
    requires isCircuitValid(c)
    requires isCertificateValidForCircuit(c,k)
    requires pos<|c|
    requires isCircuitCellAVariable(c[pos])
{
    if k[nthVariableCircuit(c,pos)]=="TRUE" then
        true
    else 
        false
}
//  lemma ValidCircuitExtension(c: circuit, ext: seq<circuitCell>)
//     requires isCircuitValid(c)
//     requires forall k :: |c| <= k <|c|+ |ext| ==> isCircuitValid'(c + ext, k)
//     ensures isCircuitValid(c + ext)
// {
//     var combined := c + ext;

//     assert forall i :: 0 <= i < |c| ==> combined[i] == c[i];
//     assert forall i :: 0 <= i < |c| ==> isCircuitValid'(c, i);
//     assert forall i :: 0 <= i < |c| && isCircuitValid'(c,i) && !isCircuitCellAVariable(c[i])==> isCircuitValid'(combined, i);
//     assert isCircuitValid(combined);
// }
predicate solveCircuit(c:circuit,k:certificate)
    requires isCircuitValid(c)
    requires isCertificateCorrectForm(k)
    requires isCertificateValidForCircuit(c,k)
    requires |c|>=1
{
    solveCircuit'(c,k,|c|-1)
}
predicate solveCircuit'(c:circuit,k:certificate,pos:nat)
    requires isCircuitValid(c)
    requires isCertificateCorrectForm(k)
    requires isCertificateValidForCircuit(c,k)
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
        case VARIABLE (x) => getValueFromCertificate(c,pos,k)
        case POZ(nr)=>
            assert  isCircuitValid'(c, pos);
            solveCircuit'(c,k,nr)
}
ghost predicate checkSatisfaction(c:circuit)
    requires isCircuitValid(c)
{
    exists k:certificate :: isCertificateCorrectForm(k) && isCertificateValidForCircuit(c,k) && |c|>=1 && solveCircuit(c,k)
}
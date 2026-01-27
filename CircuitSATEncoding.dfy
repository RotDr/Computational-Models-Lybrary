include "Certificate.dfy"
include "Circuit.dfy"
include "CKTInput.dfy"
ghost function circuitToInput (c:circuit) : seq<string>
    requires isCircuitGood(c)
{
    circuitToInput'(c,0)
}
function posToInput (e:circuitCell, poz:nat) : string
    requires isCircuitCellAPoz(e)
    requires isAGoodPoz(e,poz)
    ensures isStringAValidNumber(posToInput(e,poz))
{
    match e
        case POZ(nr) =>
            assert 0<=nr<=poz-1;
            assert poz-1-nr>=0; 
            assert poz-1-(poz-1-nr)>=0;
            natToString(poz-1-nr)
}
function inputToPos (s:string, poz:nat) : circuitCell
    requires isStringAValidNumber(s)
    requires isAGoodPozInput(s,poz)
    ensures isCircuitCellAPoz(inputToPos(s,poz)) && isAGoodPoz(inputToPos(s,poz),poz)
{
    assert poz-stringToNat(s)-1>=0;
    assert poz-stringToNat(s)-1<=poz-1; 
    assert isCircuitCellAPoz( POZ(poz-stringToNat(s)-1));
    assert isCircuitCellAPoz( POZ(poz-stringToNat(s)-1)) && isAGoodPoz(POZ(poz-stringToNat(s)-1),poz);
    POZ(poz-stringToNat(s)-1)
}
lemma PosAndPOZSymmetry1(s:string,poz:nat)
    requires isStringAValidNumber(s)
    requires isAGoodPozInput(s,poz)
    ensures posToInput(inputToPos(s,poz),poz)==s
{
    var n:=inputToPos(s,poz);
    var nr :| n==POZ(nr);
    assert nr==poz-stringToNat(s)-1;
    assert poz-1-(poz-stringToNat(s)-1)==stringToNat(s);
    stringToNatThenNatToStringIdem(s);
}
lemma PosAndPOZSymmetry2 (e:circuitCell,pos:nat)
    requires isCircuitCellAPoz(e)
    requires isAGoodPoz(e,pos)
    ensures isStringAValidNumber(posToInput(e,pos))&& isAGoodPozInput(posToInput(e,pos),pos) && inputToPos(posToInput(e,pos),pos)==e
{
    match e
        case POZ(nr) => 
            var val := pos - 1 - nr; 
            natToStringThenStringToNatIdem(val);
            assert stringToNat(posToInput(e, pos)) == val;
            assert pos - 1 - val == nr;
}

function circuitToInput' (c:circuit,poz:nat) :seq<string>
    requires poz<=|c|
    requires isCircuitGood(c)
    ensures |circuitToInput'(c,|c|)|==0
    ensures poz<|c| ==> |circuitToInput'(c,poz)|==|circuitToInput'(c,poz+1)|+1
    decreases |c|-poz
{
    if poz==|c| then 
    []
    else 
        if isCircuitCellAPoz(c[poz]) then
            assert isCircuitGood'(c[poz],poz);
            [posToInput(c[poz],poz)]+circuitToInput'(c,poz+1)
        else
            assert isCircuitGood'(c[poz],poz);
            [gateToString(c[poz])]+circuitToInput'(c,poz+1)
}

lemma sameCircuitToInputLength(c: circuit, poz: nat)
    requires isCircuitGood(c)
    requires poz <= |c|
    ensures |circuitToInput'(c, poz)| == |c| - poz
    decreases |c| - poz
{
    if poz == |c| {
    } else {
        sameCircuitToInputLength(c, poz + 1);
    }
}

lemma sameFullCircuitToInputLength(c: circuit)
    requires isCircuitGood(c)
    ensures |circuitToInput(c)| == |c|
{
    sameCircuitToInputLength(c, 0);
}
lemma aValidCircuitIsGood(c:circuit)
 requires isCircuitValid(c)
    ensures forall pos:nat::pos<|c| && isCircuitCellAPoz(c[pos]) ==> isAGoodPoz(c[pos],pos)
    ensures  forall pos:nat::pos<|c| && isCircuitCellAVariable(c[pos]) ==> isAGoodVariableCircuit(c[pos])
{
    forall pos:nat | pos<|c|
        ensures pos<|c| && isCircuitCellAPoz(c[pos]) ==> isAGoodPoz(c[pos],pos)
        ensures pos<|c| && isCircuitCellAVariable(c[pos]) ==> isAGoodVariableCircuit(c[pos])
    {
        aValidCircuitIsGood'(c,pos);
    }
}
lemma aValidCircuitIsGood' (c:circuit,pos:nat)
    requires isCircuitValid(c)
    ensures pos<|c| && isCircuitCellAPoz(c[pos]) ==> isAGoodPoz(c[pos],pos)
    ensures  pos<|c| && isCircuitCellAVariable(c[pos]) ==> isAGoodVariableCircuit(c[pos])
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
        if isCircuitCellAVariable(c[pos])
        {
            assert isAGoodVariableCircuit(c[pos]);
        }
    }
}
function gateToString(e:circuitCell) : string
    requires !isCircuitCellAPoz(e)
    requires isCircuitCellAVariable(e) ==> isAGoodVariableCircuit(e)
    ensures !isStringAValidNumber(gateToString(e))
    ensures isCircuitCellAVariable(e) ==> !(gateToString(e) in ReservedWords)
{
    match e
        case AND => "AND"
        case OR => "OR"
        case NOT => "NOT"
        case VARIABLE(x) => x

}
function stringToGate(s:string):circuitCell
    requires !isStringAValidNumber(s)
    requires !(s in ["AND","OR","NOT"]) ==> !(s in ReservedWords)
    ensures !(s in ReservedWords) ==> isCircuitCellAVariable(stringToGate(s)) && isAGoodVariableCircuit(stringToGate(s))
{
    match s
        case "AND" => AND
        case "OR" => OR
        case "NOT" => NOT
        case x => VARIABLE(x)
}
lemma gateAndStringSymmetry1(e:circuitCell)
    requires !isCircuitCellAPoz(e)
    requires isCircuitCellAVariable(e) ==> isAGoodVariableCircuit(e)
    ensures !isStringAValidNumber(gateToString(e)) && stringToGate(gateToString(e))==e
{

}
lemma gateAndStringSymmetry2(s:string)
    requires !isStringAValidNumber(s)
    requires !(s in ["AND","OR","NOT"]) ==> !(s in ReservedWords)
    ensures gateToString(stringToGate(s))==s
{

}
function inputToCircuit (input:seq<string>) : circuit
    requires isInputGoodForCKT(input)

 {
     inputToCircuit'(input,0)
 }
function inputToCircuit' (input:seq<string>,pos:nat) : circuit
    requires pos<=|input|
    requires isInputGoodForCKT(input)
    decreases |input|-pos
    ensures |inputToCircuit'(input,|input|)|==0
    ensures pos<|input| ==> |inputToCircuit'(input,pos)|==|inputToCircuit'(input,pos+1)|+1
{
    if pos==|input| then []
    else
        if isStringAValidNumber(input[pos]) then 
            [inputToPos(input[pos],pos)]+inputToCircuit'(input,pos+1)
        else
            [stringToGate(input[pos])]+inputToCircuit'(input,pos+1)
}
lemma sameInputToCircuitLength(input:seq<string>, poz: nat)
    requires isInputGoodForCKT(input)
    requires poz <= |input|
    ensures |inputToCircuit'(input, poz)| == |input| - poz
    decreases |input| - poz
{
    if poz == |input| {
    } else {
        sameInputToCircuitLength(input, poz + 1);
    }
}

lemma sameFullInputToCircuitLength(input:seq<string>)
    requires isInputGoodForCKT(input)
    ensures |inputToCircuit(input)| == |input|
{
    sameInputToCircuitLength(input, 0);
}
ghost predicate isInputGoodForCKT (input:seq<string>)
{
    (forall pos:nat::pos<|input| && isStringAValidNumber(input[pos]) ==> isAGoodPozInput(input[pos],pos)) &&
    forall pos:nat::pos<|input| && !isStringAValidNumber(input[pos]) && !(input[pos] in ["AND","OR","NOT"])==> !(input[pos] in ReservedWords) 
}
lemma aCKTInputIsGood (input:seq<string>)
    requires isInputCKT(input)
    ensures isInputGoodForCKT(input)
{
     forall pos:nat | pos<|input|
        ensures pos<|input| && isStringAValidNumber(input[pos]) ==> isAGoodPozInput(input[pos],pos)
        ensures pos<|input| && !isStringAValidNumber(input[pos]) && !(input[pos] in ["AND","OR","NOT"]) ==> !(input[pos] in ReservedWords)
    {
        assert isInputCKT'(input,pos);
        if isStringAValidNumber(input[pos])
        {
            assert isAGoodPozInput(input[pos],pos);
        }
    }
}

lemma inputCircuitSymmetry1(input: seq<string>)
    requires isInputGoodForCKT(input)
    ensures isCircuitGood(inputToCircuit(input)) 
    ensures circuitToInput(inputToCircuit(input)) == input 
{
    sameFullInputToCircuitLength(input);
    assert |inputToCircuit(input)|==|input|;
    FullInputCircuitSymmetry(input, 0);
}
lemma Lemma_InputToCircuit_IsGood(input: seq<string>)
    requires isInputGoodForCKT(input)
    ensures isCircuitGood(inputToCircuit(input))
{
    var c := inputToCircuit(input);
    forall poz | 0 <= poz < |c|
        ensures isCircuitGood'(c[poz], poz)
    {
        sameFullInputToCircuitLength(input);
        Lemma_NthElement_Bridge(input, 0, poz); 

        if isStringAValidNumber(input[poz]) {
            assert c[poz] == inputToPos(input[poz], poz);
        } else {
            assert c[poz] == stringToGate(input[poz]);
        }
    }
}

lemma Lemma_NthElement_Bridge(input: seq<string>, current: nat, target: nat)
    requires isInputGoodForCKT(input)
    requires current <= target < |input|
    ensures var c_sub := inputToCircuit'(input, current);
            target - current < |c_sub| &&
            (if isStringAValidNumber(input[target]) 
             then c_sub[target - current] == inputToPos(input[target], target) 
             else c_sub[target - current] == stringToGate(input[target]))
    decreases target - current
{
    if current == target {
    } else {
        Lemma_NthElement_Bridge(input, current + 1, target);
    }
}
lemma NthElementBridge(c:circuit, current:nat, target:nat)
    requires isCircuitGood(c)
    requires current <= target <|c|
    ensures var i_sub := circuitToInput'(c,current);
            target-current<|i_sub| &&
            (
                if isCircuitCellAPoz(c[target])
                then i_sub[target-current] == posToInput(c[target],target)
                else i_sub[target-current] == gateToString(c[target])
            )
    decreases target - current
{
 if current == target {
    } else {
        NthElementBridge(c, current + 1, target);
    }
}
lemma FullInputCircuitSymmetry(input: seq<string>, k: nat)
    requires isInputGoodForCKT(input) && k <= |input|
    requires |inputToCircuit(input)|==|input|
    ensures isCircuitGood(inputToCircuit(input))
    ensures var c := inputToCircuit(input);
            assert |c|==|input|;
            (forall p :: k <= p < |c| ==> isCircuitGood'(c[p], p)) &&
            circuitToInput'(c, k) == input[k..]
    decreases |input| - k
{
    Lemma_InputToCircuit_IsGood(input);
    var c := inputToCircuit(input);

    if k < |input| {

        FullInputCircuitSymmetry(input, k + 1);
        if isStringAValidNumber(input[k]) {
            Lemma_NthElement_Bridge(input, 0, k);
            PosAndPOZSymmetry1(input[k], k); 
        } else {
            Lemma_NthElement_Bridge(input, 0, k);
            gateAndStringSymmetry2(input[k]); 
        }
        
    }
}
// lemma validCircuitGivesCKTInput(c:circuit)
//     requires isCircuitValid(c)
//     ensures  isCircuitGood(c) && isInputCKT(circuitToInput(c))
// {
//     aValidCircuitIsGood(c);
//     var input:= circuitToInput(c);
//     sameFullCircuitToInputLength(c);
//     assert |c|==|input|;
//     forall i|0<=i< |input|
//         ensures isInputCKT'(input,i)
//         {
//             NthElementBridge(c,0,i);
//                 match c[i]
//                     case POZ(n)=>
//                     {

//                         assert isCircuitValid'(c,i);
//                         assert n<i;
//                         assert !isCircuitCellAPoz(c[n]);
//                         assert input[i]==posToInput(c[i],i);
//                         assert input[i]==natToString(i-1-n);
//                         assert isStringAValidNumber(input[i]);
//                         natToStringThenStringToNatIdem(i-1-n);
//                         assert stringToNat(input[i])==i-1-n;
//                         var nr := i -stringToNat(input[i])-1;
//                         assert nr==i-(i-1-n)-1;
//                         assert nr==n;
//                         NthElementBridge(c,0,n);
//                         assert input[n]==gateToString(c[n]);
//                         assert !isStringAValidNumber(input[n]);
//                         assert  isStringAValidPos(input, i);
//                     }
//                     case AND=>
//                     {
//                         assert isCircuitValid'(c, i);
//                         NthElementBridge(c, 0, i-1);
//                         NthElementBridge(c, 0, i-2);
                        
//                         assert isStringAValidNumber(input[i-1]) && isStringAValidPos(input, i-1);
//                         assert isStringAValidNumber(input[i-2]) && isStringAValidPos(input, i-2);
//                             }
//                     case OR=>
//                     {
//                             assert isCircuitValid'(c, i);
//                             NthElementBridge(c, 0, i-1);
//                             NthElementBridge(c, 0, i-2);
                            
//                             assert isStringAValidNumber(input[i-1]) && isStringAValidPos(input, i-1);
//                             assert isStringAValidNumber(input[i-2]) && isStringAValidPos(input, i-2);

//                     }
//                     case NOT=>
//                     {
//                         assert isCircuitValid'(c, i);
//                         NthElementBridge(c, 0, i-1);
//                         assert isCircuitCellAPoz(c[i-1]);
//                         assert isStringAValidNumber(input[i-1]) && isStringAValidPos(input, i-1);
//                     }
//                     case VARIABLE(X)=>
//                     {
//                         assert input[i] == gateToString(c[i]);
//                         assert !isStringAValidNumber(input[i]);
//                         assert !(input[i] in ReservedWords);
//                     }
//             }
// }
lemma validCircuitGivesCKTInput(c: circuit)
    requires isCircuitValid(c)
    ensures isCircuitGood(c) && isInputCKT(circuitToInput(c))
{
    aValidCircuitIsGood(c);
    var input:= circuitToInput(c);
    sameFullCircuitToInputLength(c);
    assert |c|==|input|;

    forall i | 0<=i<|input|
        ensures isInputCKT'(input,i)
    {
        NthElementBridge(c,0,i);
        match c[i]
            case POZ(n) =>
                assert isCircuitValid'(c,i);
                assert n<i;
                assert !isCircuitCellAPoz(c[n]);


                var nr:=i-1-stringToNat(input[i]);
                // assert nr == n;
                // assert input[n] == gateToString(c[n]);

                // assert !isStringAValidNumber(input[n]);
                // assert isStringAValidPos(input, i);
            case AND=>
                assert isCircuitValid'(c, i);
                NthElementBridge(c, 0, i-1);
                NthElementBridge(c, 0, i-2);
                
                assert isStringAValidNumber(input[i-1]) && isStringAValidPos(input, i-1);
                assert isStringAValidNumber(input[i-2]) && isStringAValidPos(input, i-2);
            case OR =>
                assert isCircuitValid'(c, i);
                NthElementBridge(c, 0, i-1);
                NthElementBridge(c, 0, i-2);
                
                assert isStringAValidNumber(input[i-1]) && isStringAValidPos(input, i-1);
                assert isStringAValidNumber(input[i-2]) && isStringAValidPos(input, i-2);
            case NOT =>
                assert isCircuitValid'(c, i);
                NthElementBridge(c, 0, i-1);
                assert isStringAValidNumber(input[i-1]) && isStringAValidPos(input, i-1);
         
    }
}
lemma cktInputGivesValidCircuit(input:seq<string>)
    requires isInputCKT(input)
    ensures isInputGoodForCKT(input) && isCircuitValid(inputToCircuit(input))
{
    aCKTInputIsGood(input);

    var c := inputToCircuit(input);
    sameFullInputToCircuitLength(input);
    assert |c| == |input|;
    forall i | 0 <= i < |c|
        ensures isCircuitValid'(c, i)
    {
        Lemma_NthElement_Bridge(input, 0, i);
        assert isInputCKT'(input, i); 

        if isStringAValidNumber(input[i]) {

            var s := input[i];
            var nr := i - stringToNat(s) - 1;

            assert c[i] == inputToPos(s, i);

            assert isStringAValidPos(input, i); 
            assert !isStringAValidNumber(input[nr]);

            Lemma_NthElement_Bridge(input, 0, nr);
            assert c[nr] == stringToGate(input[nr]); 
            assert !isCircuitCellAPoz(c[nr]);

        } else {

            assert c[i] == stringToGate(input[i]);

            if input[i] == "AND" {
                assert i > 2; 
                Lemma_NthElement_Bridge(input, 0, i-1);
                Lemma_NthElement_Bridge(input, 0, i-2);
                
                assert isStringAValidNumber(input[i-1]); 
                assert isStringAValidNumber(input[i-2]);

                assert c[i-1] == inputToPos(input[i-1], i-1);
                assert c[i-2] == inputToPos(input[i-2], i-2);
                assert isCircuitCellAPoz(c[i-1]) && isCircuitCellAPoz(c[i-2]);

            } else if input[i] == "OR" {
                assert i > 2;
                Lemma_NthElement_Bridge(input, 0, i-1);
                Lemma_NthElement_Bridge(input, 0, i-2);
                assert isCircuitCellAPoz(c[i-1]) && isCircuitCellAPoz(c[i-2]);

            } else if input[i] == "NOT" {
                assert i > 1;
                Lemma_NthElement_Bridge(input, 0, i-1);
                assert isCircuitCellAPoz(c[i-1]);

            } else {
            }
        }
    }
}

// lemma inputCircuitSymmetry2 (c:circuit)
//     requires isCircuitGood(c)
//     ensures isCircuitGood(c) && isInputGoodForCKT(circuitToInput(c)) && inputToCircuit(circuitToInput(c))==c 
// {

// }
// lemma aCKTInputGivesAValidCircuit (input:seq<string>)
//     requires isInputCKT(input)
//     ensures isCircuitValid(inputToCircuit(input))
// {
//     matchInputCircuit (input,inputToCircuit(input),|input|-1);
// }
// lemma matchInputCircuit (input:seq<string>,c:circuit,pos:int)
//      requires isInputCKT(input)
//      requires -1<=pos<|input| 
//      ensures 0<=pos<|c| ==> isCircuitValid'(c,pos)
//      decreases pos 
// {
//     if pos ==-1{
//         assert c==[];
//     }
//     else
//     {
//         match input[pos] {
//             case "AND" => {
//                 assert isInputCKT'(input,pos);
//                 var prefix_c := inputToCircuit'(input, pos - 3);
//                 matchInputCircuit(input, prefix_c, pos - 3);
//                 var pos1:=inputToPos(input, pos - 2);
//                 var pos2:= inputToPos(input, pos - 1);
//                 var ext := [pos1,pos2, AND];
//                 assert match pos1
//                         case POZ(nr) => nr==(pos-2)-stringToNat(input[pos-2])-1 && 0<=nr<(pos-2-1);
//                 assert match pos2
//                         case POZ(nr) => nr==(pos-1)-stringToNat(input[pos-1])-1 && 0<=nr<(pos-1-1);
//                 assert c== inputToCircuit'(input,pos-3)+[inputToPos(input,pos-2),inputToPos(input,pos-1),AND];
//                 assert c == prefix_c + ext;
//                 Lemma_ValidCircuitExtension(prefix_c, ext);
//             }
//             case "OR" => {
//                 var prefix_c := inputToCircuit'(input, pos - 3);
//                 matchInputCircuit(input, prefix_c, pos - 3);
//                 var ext := [inputToPos(input, pos - 2), inputToPos(input, pos - 1), OR];
//                 assert c == prefix_c + ext;
//                 Lemma_ValidCircuitExtension(prefix_c, ext);
//             }
//             case "NOT" => {
//                 var prefix_c := inputToCircuit'(input, pos - 2);
//                 matchInputCircuit(input, prefix_c, pos - 2);
//                 var ext := [inputToPos(input, pos - 1), NOT];
//                 assert c == prefix_c + ext;
//                 Lemma_ValidCircuitExtension(prefix_c, ext);
//             }
//             case x => {
//                 var prefix_c := inputToCircuit'(input, pos - 1);
//                 matchInputCircuit(input, prefix_c, pos - 1);
//                 var ext := if isStringAValidNumber(x) then [inputToPos(input, pos)] else [VARIABLE(x)];
//                 assert c == prefix_c + ext;
//                 Lemma_ValidCircuitExtension(prefix_c, ext);
//             }
//         }
//     }
// }
// ghost predicate isThatActuallyTheCKTSATLanguage (l:Language) 
// {
//     (forall input:seq<string> :: (input in l) ==> ( isInputCKT(input) && isCircuitValid(inputToCircuit(input)) && checkSatisfaction(inputToCircuit(input))
//     ))
//     &&
//     (forall c:circuit :: isCircuitValid(c) && checkSatisfaction(c) ==>
//     (circuitToInput(c) in l))
// }

// predicate isCircuitValid'(c:circuit, pos:nat)
//     requires pos<|c|
// {
//     match c[pos]
//             case AND => 2<pos<|c| && isCircuitCellAPoz(c[pos-1]) && isCircuitCellAPoz(c[pos-2])
//             case OR => 2<pos<|c|  && isCircuitCellAPoz(c[pos-1]) && isCircuitCellAPoz(c[pos-2])
//             case NOT => 1<pos<|c| && isCircuitCellAPoz(c[pos-1]) 
//             case VARIABLE (x) => x!="true" && x!="false"  
//             case POZ(nr) => isCircuitCellAValidPoz(c[pos],pos,c) && 0<pos
// }
predicate areTwoCircuitsTheSame (c1:circuit,c2:circuit)
{
    |c1|==|c2| && forall pos:nat::pos<|c1| ==> c1[pos]==c2[pos]
}
// lemma sameSizeCircuitToInput(c:circuit)
//     requires forall poz:nat::poz<|c| ==> isThatPOZValid(c,poz) 
//     ensures |c|==|circuitToInput(c)|
//     ensures forall poz:nat::poz<|c| ==> isThatPOZValid(c,poz) 
// {
//     if c==[] {
//         assert |c|==0;
//         assert circuitToInput(c)==circuitToInput'(c,0);
//         assert circuitToInput'(c,0)==circuitToInput'(c,|c|);
//         assert |circuitToInput'(c,|c|)|==0;
//         assert |circuitToInput(c)|==0;
//         assert |c|==0;
//         assert |circuitToInput(c)|==|c|;
//     }
//     else
//     {
//         assert forall poz:nat::poz<|c|-1 ==> isThatPOZValid(c,poz);
//         assert forall poz:nat::poz<|c|-1 ==> c[poz]==c[..|c|-1][poz];
//         assert forall poz:nat::poz<|c|-1 && c[poz]==c[..|c|-1][poz] ==> isThatPOZValid(c[..|c|-1],poz);
//         assert forall poz:nat::poz<|c|-1 ==> isThatPOZValid(c[..|c|-1],poz);
//         sameSizeCircuitToInput(c[..|c|-1]);
//     }
// }
// lemma circuitAndInput()
//     ensures forall c:circuit:: isCircuitValid(c) ==> (match inputToCircuit(circuitToInput(c))
//                                                         case None => false
//                                                         case Some(c2)=> areTwoCircuitsTheSame(c,c2) )
// {
//     var c :| isCircuitValid(c);
//     var input:| input==circuitToInput(c);

//     assert forall pos:nat:: pos<|c| ==> match c[pos]
//                                             case AND=> input[pos]=="AND"
//                                             case OR=> input[pos]=="OR"
//                                             case NOT=> input[pos]=="NOT"
//                                             case POZ(nr)=> input[pos]==natToString(pos-nr-1);
                                            
// }
// include "Certificate.dfy"
// include "Circuit.dfy"
// include "CKTInput.dfy"
// function circuitToInput (c:circuit) : seq<string>
//     requires isCircuitGood(c)
// {
//     circuitToInput'(c,0)
// }
// function circuitCellToString (e:circuitCell) : string
// {
//     match e 
//         case AND => "AND"
//         case OR => "OR"
//         case NOT => "NOT"
//         case VARIABLE(x) => "VARIABLE"
//         case POZ(nr) =>
//             natToString(nr)
// }
// lemma stringToCircuitCellToStringIsTheSame (s:string,pos:nat)
//     requires !(s in ["AND","OR","NOT","VARIABLE"]) ==> isStringAValidNumber(s)
//     ensures circuitCellToString(stringToCircuitCell(s,pos))==s
// {
//     var c:=stringToCircuitCell(s,pos);
//     if isStringAValidNumber(s)
//     {
//         assert c==POZ(stringToNat(s));
//         assert isCircuitCellAPoz(c);
//         var s2:=circuitCellToString(c);
//         assert s2==natToString(stringToNat(s));
//         stringToNatThenNatToStringIdem(s);
//         assert s2==s;
//     }
// }
// function circuitToInput' (c:circuit,pos:nat) :seq<string>
//     requires pos<=|c|
//     requires isCircuitGood(c)
//     ensures |circuitToInput'(c,|c|)|==0
//     ensures pos<|c| ==> |circuitToInput'(c,pos)|==|circuitToInput'(c,pos+1)|+1
//     decreases |c|-pos
// {
//     if pos==|c| then 
//     []
//     else 
//         [circuitCellToString(c[pos])]+circuitToInput'(c,pos+1)
// }

// lemma sameCircuitToInputLength(c: circuit, poz: nat)
//     requires isCircuitGood(c)
//     requires poz <= |c|
//     ensures |circuitToInput'(c, poz)| == |c| - poz
//     decreases |c| - poz
// {
//     if poz == |c| {
//     } else {
//         sameCircuitToInputLength(c, poz + 1);
//     }
// }

// lemma sameFullCircuitToInputLength(c: circuit)
//     requires isCircuitGood(c)
//     ensures |circuitToInput(c)| == |c|
// {
//     sameCircuitToInputLength(c, 0);
// }

// function stringToCircuitCell (s:string,nr:nat):circuitCell
//     requires !(s in ["AND","OR","NOT","VARIABLE"]) ==> isStringAValidNumber(s) 
// {
//     match s
//         case "AND" => AND
//         case "OR" => OR
//         case "NOT" => NOT
//         case "VARIABLE" => VARIABLE("VARIABLE "+natToString(nr))
//         case _ => POZ(stringToNat(s))
// }

// function inputToCircuit (input:seq<string>) : circuit
//     requires isInputGoodForCKT(input)

//  {
//      inputToCircuit'(input,0)
//  }
// function inputToCircuit' (input:seq<string>,pos:nat) : circuit
//     requires pos<=|input|
//     requires isInputGoodForCKT(input)
//     decreases |input|-pos
//     ensures |inputToCircuit'(input,|input|)|==0
//     ensures pos<|input| ==> |inputToCircuit'(input,pos)|==|inputToCircuit'(input,pos+1)|+1
// {
//     if pos==|input| then []
//     else
//         [stringToCircuitCell(input[pos],pos)]+inputToCircuit'(input,pos+1)
// }
// lemma sameInputToCircuitLength(input:seq<string>, poz: nat)
//     requires isInputGoodForCKT(input)
//     requires poz <= |input|
//     ensures |inputToCircuit'(input, poz)| == |input| - poz
//     decreases |input| - poz
// {
//     if poz == |input| {
//     } else {
//         sameInputToCircuitLength(input, poz + 1);
//     }
// }

// lemma sameFullInputToCircuitLength(input:seq<string>)
//     requires isInputGoodForCKT(input)
//     ensures |inputToCircuit(input)| == |input|
// {
//     sameInputToCircuitLength(input, 0);
// }

// lemma InputToCircuit_IsGood(input: seq<string>)
//     requires isInputGoodForCKT(input)
//     ensures isCircuitGood(inputToCircuit(input))
// {
//     var c := inputToCircuit(input);
//     for pos:=0 to |c|
//         invariant forall poz:nat::0<=poz<pos ==>  isCircuitGood'(c[poz], poz) 
//     {
//             sameFullInputToCircuitLength(input);
//             Lemma_NthElement_Bridge(input, 0, pos); 
//             assert c[pos] == stringToCircuitCell(input[pos], pos);
//             if (isStringAValidNumber(input[pos]))
//             {
//                 assert isStringGoodForCKT(input[pos],pos);
//                 assert stringToNat(input[pos])<pos;
//                 assert isCircuitCellAPoz(c[pos]);
//                 assert match c[pos]
//                         case POZ(nr) => nr== stringToNat(input[pos]);
//                 assert  match c[pos]
//                         case POZ(nr) => nr<pos;
//             }
//     }
    
// }

// lemma Lemma_NthElement_Bridge(input: seq<string>, current: nat, target: nat)
//     requires isInputGoodForCKT(input)
//     requires current <= target < |input|
//     ensures var c_sub := inputToCircuit'(input, current);
//             target - current < |c_sub| &&
//             c_sub[target - current] == stringToCircuitCell(input[target],target)
//     decreases target - current
// {
//     if current == target {
//     } else {
//         Lemma_NthElement_Bridge(input, current + 1, target);
//     }
// }
// lemma NthElementBridge(c:circuit, current:nat, target:nat)
//     requires isCircuitGood(c)
//     requires current <= target <|c|
//     ensures var i_sub := circuitToInput'(c,current);
//             target-current<|i_sub| &&
//             (
//                 i_sub[target-current] == circuitCellToString(c[target])
//             )
//     decreases target - current
// {
//  if current == target {
//     } else {
//         NthElementBridge(c, current + 1, target);
//     }
// }
// lemma InputToCircuitSymmetry(input: seq<string>)
//     requires isInputGoodForCKT(input)
//     ensures isCircuitGood(inputToCircuit(input)) 
//     ensures circuitToInput(inputToCircuit(input)) == input 
// {
//     sameFullInputToCircuitLength(input);
//     assert |inputToCircuit(input)|==|input|;
//     FullInputToCircuitSymmetry(input, 0);
// }
// lemma FullInputToCircuitSymmetry(input: seq<string>, k: nat)
//     requires isInputGoodForCKT(input) && k <= |input|
//     requires |inputToCircuit(input)| == |input|
//     ensures isCircuitGood(inputToCircuit(input))
//     ensures var c := inputToCircuit(input);
//             circuitToInput'(c, k) == input[k..]
//     decreases |input| - k
// {
//     InputToCircuit_IsGood(input);
//     var c := inputToCircuit(input);
    
//     if k == |input| {
//     } else {

//         Lemma_NthElement_Bridge(input, 0, k); 
//         stringToCircuitCellToStringIsTheSame(input[k],k);
//         assert c[k] == stringToCircuitCell(input[k], k);
//         assert circuitCellToString(c[k]) == input[k]; 
        
//     }
// }
// lemma Lemma_NumberInputImpliesValidPos(input: seq<string>, k: nat)
//     requires k < |input|
//     requires isInputCKT'(input, k)
//     requires isStringAValidNumber(input[k])
//     ensures isStringAValidPos(input, k)
// {
//     assert match input[k]
//         case "AND" => false
//         case "OR" => false
//         case "NOT" => false
//         case "VARIABLE" => false
//         case _ => true;
// }

// // 
// // lemma validCircuitGivesCKTInput(c:circuit) 
// //     requires isCircuitValid(c)
// //     ensures isCircuitGood(c) && isInputCKT(circuitToInput(c))
// // {
// //     aValidCircuitIsGood(c);
// //     var input := circuitToInput(c);
// //     sameFullCircuitToInputLength(c);
// //     assert |c| == |input|;
    
// //     for i := 0 to |input|
// //         invariant forall poz:nat :: poz < i ==> isInputCKT'(input, poz)
// //     {
// //         NthElementBridge(c, 0, i);
// //         assert isCircuitValid'(c, i);
        
// //         match c[i]
// //             case POZ(n) => {
// //                 assert n < i;
// //                 assert !isCircuitCellAPoz(c[n]);
// //                 NthElementBridge(c, 0, n); 
// //                 assert input[n] == circuitCellToString(c[n]);
// //                 assert !isStringAValidNumber(input[n]); 
// //                 natToStringThenStringToNatIdem(n);
// //                 assert isStringAValidPos(input, i);
// //                 assert isInputCKT'(input, i);
// //             }
// //             case AND => {
// //                 assert i >= 2;  
// //                 assert isCircuitCellAPoz(c[i-1]);
// //                 assert isCircuitCellAPoz(c[i-2]);
                
// //                 NthElementBridge(c, 0, i-1);
// //                 NthElementBridge(c, 0, i-2);
                
// //                 var s1 := input[i-1];
// //                 var s2 := input[i-2];
                
// //                 assert match c[i-1] case POZ(_) => isStringAValidNumber(s1);
// //                 assert match c[i-2] case POZ(_) => isStringAValidNumber(s2);
                
// //                 assert isStringAValidNumber(s1);
// //                 assert isStringAValidNumber(s2);
// //                 assert isInputCKT'(input, i);
// //             }
// //             case OR => {
// //                 assert i >= 2;
// //                 assert isCircuitCellAPoz(c[i-1]);
// //                 assert isCircuitCellAPoz(c[i-2]);
                
// //                 NthElementBridge(c, 0, i-1);
// //                 NthElementBridge(c, 0, i-2);
                
// //                 var s1 := input[i-1];
// //                 var s2 := input[i-2];
                
// //                 assert match c[i-1] case POZ(_) => isStringAValidNumber(s1);
// //                 assert match c[i-2] case POZ(_) => isStringAValidNumber(s2);
                
// //                 assert isStringAValidNumber(s1);
// //                 assert isStringAValidNumber(s2);
// //                 assert isInputCKT'(input, i);
// //             }
// //             case NOT => {
// //                 assert i >= 1;
// //                 assert isCircuitCellAPoz(c[i-1]);
                
// //                 NthElementBridge(c, 0, i-1);
// //                 var s1 := input[i-1];
                
// //                 assert match c[i-1] case POZ(_) => isStringAValidNumber(s1);
// //                 assert isStringAValidNumber(s1);
                
// //                 assert isInputCKT'(input, i);
// //             }
// //             case VARIABLE(X) => {
// //                 assert isInputCKT'(input, i);
// //             }
// //     }
// // }

// lemma PozCellGivesValidNumber(c: circuit, pos: nat, input: seq<string>)
//     requires isCircuitValid(c)
//     requires pos < |c|
//     requires isCircuitCellAPoz(c[pos])
//     requires isCircuitGood(c)
//     requires input == circuitToInput(c)
//     requires |input| == |c|
//     ensures isStringAValidNumber(input[pos])
// {
//     NthElementBridge(c, 0, pos);
//     assert input[pos] == circuitCellToString(c[pos]);
// }

// lemma cktInputGivesValidCircuit(input:seq<string>)
//     requires isInputCKT(input)
//     ensures isInputGoodForCKT(input) && isCircuitValid(inputToCircuit(input))
// {
//     aCKTInputIsGood(input);

//     var c := inputToCircuit(input);
//     sameFullInputToCircuitLength(input);
//     assert |c| == |input|;
//     forall i | 0 <= i < |c|
//         ensures isCircuitValid'(c, i)
//     {
//         Lemma_NthElement_Bridge(input, 0, i);
//         assert isInputCKT'(input, i); 

//         if isStringAValidNumber(input[i]) {

//             var s := input[i];
//             var nr := i - stringToNat(s) - 1;

//             assert c[i] == inputToPos(s, i);

//             assert isStringAValidPos(input, i); 
//             assert !isStringAValidNumber(input[nr]);

//             Lemma_NthElement_Bridge(input, 0, nr);
//             assert c[nr] == stringToGate(input[nr]); 
//             assert !isCircuitCellAPoz(c[nr]);

//         } else {

//             assert c[i] == stringToGate(input[i]);

//             if input[i] == "AND" {
//                 assert i > 2; 
//                 Lemma_NthElement_Bridge(input, 0, i-1);
//                 Lemma_NthElement_Bridge(input, 0, i-2);
                
//                 assert isStringAValidNumber(input[i-1]); 
//                 assert isStringAValidNumber(input[i-2]);

//                 assert c[i-1] == inputToPos(input[i-1], i-1);
//                 assert c[i-2] == inputToPos(input[i-2], i-2);
//                 assert isCircuitCellAPoz(c[i-1]) && isCircuitCellAPoz(c[i-2]);

//             } else if input[i] == "OR" {
//                 assert i > 2;
//                 Lemma_NthElement_Bridge(input, 0, i-1);
//                 Lemma_NthElement_Bridge(input, 0, i-2);
//                 assert isCircuitCellAPoz(c[i-1]) && isCircuitCellAPoz(c[i-2]);

//             } else if input[i] == "NOT" {
//                 assert i > 1;
//                 Lemma_NthElement_Bridge(input, 0, i-1);
//                 assert isCircuitCellAPoz(c[i-1]);

//             } else {
//             }
//         }
//     }
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
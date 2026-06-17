include "NDTM.dfy"


ghost predicate isTransitionsDeterministic(delta:Transitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols)
    requires isTapeSymbolsValid(inputS,addTapeS)
    requires isTransitionsValid(delta,inputS,addTapeS)
{
  forall q0:State,s0:Symbol :: Key(q0,s0) in delta.Keys ==> |delta[Key(q0,s0)]|==1
}
type DeterministicTransitions = map<Key,Action>


ghost function fromNDTMtoDTM (delta:Transitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols) : DeterministicTransitions
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isTransitionsValid(delta,inputS,addTapeS)
  requires isTransitionsDeterministic(delta,inputS,addTapeS)
  ensures var delta':=fromNDTMtoDTM (delta,inputS,addTapeS);
           isDeterministicTransitionsValid(delta',inputS,addTapeS)
{
  fromNDTMtoDTM'(delta,inputS,addTapeS,delta.Keys)
}
ghost function fromNDTMtoDTM'(delta:Transitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,keys:set<Key>) : DeterministicTransitions
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isTransitionsValid(delta,inputS,addTapeS)
  requires isTransitionsDeterministic(delta,inputS,addTapeS)
  requires keys <= delta.Keys
  ensures keys <= delta.Keys
  ensures var delta':=fromNDTMtoDTM' (delta,inputS,addTapeS,keys);
           isDeterministicTransitionsValid(delta',inputS,addTapeS)
    ensures var chei := fromNDTMtoDTM'(delta, inputS, addTapeS, keys); 
          chei.Keys == keys && 
          forall k :: k in keys ==> [chei[k]] == delta[k]

   decreases keys

{
  if |keys|==0 then
    map[]
  else
    var s:| s in keys;
    assert keys<= delta.Keys;
    assert s in keys;
    assert isTransitionsDeterministic(delta,inputS,addTapeS);
    assert forall q0:State,s0:Symbol :: Key(q0,s0) in delta.Keys ==> |delta[Key(q0,s0)]|==1;
    assert forall k:Key:: k in delta.Keys ==> (exists q0:State,s0:Symbol :: k==Key(q0,s0) && Key(q0,s0) in delta.Keys);
    assert forall k:Key :: k in delta.Keys ==> |delta[k]|==1;
    assert forall q0:State,s0:Symbol :: Key(q0,s0) in delta.Keys ==> ((s0 in inputS+addTapeS) && 
                                                              |delta[Key(q0,s0)]|>=1 &&
                                                            (forall i:Action:: i in delta[Key(q0,s0)] ==>
                                                                                                          match i 
                                                                                                            case Action(_,s1,_) => s1 in inputS+addTapeS));
    assert forall q0:State,s0:Symbol :: Key(q0,s0) in delta.Keys ==> delta[Key(q0,s0)][0] in delta[Key(q0,s0)];
    assert forall q0:State,s0:Symbol :: Key(q0,s0) in delta.Keys ==> ((s0 in inputS+addTapeS) && 
                                                                              match delta[s][0]
                                                                                    case Action(_,s1,_) => s1 in inputS+addTapeS);
    fromNDTMtoDTM'(delta, inputS, addTapeS, keys - {s})[s := delta[s][0]]
}
ghost predicate isDeterministicTransitionsValid(delta:DeterministicTransitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols)
  requires isTapeSymbolsValid(inputS,addTapeS)
{
  forall q0:State,s0:Symbol :: Key(q0,s0) in delta.Keys ==> ((s0 in inputS+addTapeS) && 
                                                            (match delta[Key(q0,s0)]
                                                              case Action(_,s1,_) => s1 in inputS+addTapeS))
}
ghost function fromDTMtoNDTM (delta:DeterministicTransitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols) : Transitions
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isDeterministicTransitionsValid(delta,inputS,addTapeS)
{
  fromDTMtoNDTM'(delta,inputS,addTapeS,delta.Keys)
}
ghost function fromDTMtoNDTM'(delta:DeterministicTransitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,keys:set<Key>) : Transitions
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isDeterministicTransitionsValid(delta,inputS,addTapeS)
  requires keys <= delta.Keys
  ensures keys <= delta.Keys
  ensures var chei := fromDTMtoNDTM'(delta, inputS, addTapeS, keys); 
          chei.Keys == keys && forall k :: k in keys ==> chei[k] == [delta[k]]
   decreases keys

{
  if |keys|==0 then
    map[]
  else
    var s:| s in keys;
    assert keys<= delta.Keys;
    assert s in keys;
    fromDTMtoNDTM'(delta, inputS, addTapeS, keys - {s})[s := [delta[s]]]
}
lemma aDTMisAValidNDTM (delta:DeterministicTransitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols)
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isDeterministicTransitionsValid(delta,inputS,addTapeS)
  ensures  isTransitionsValid(fromDTMtoNDTM(delta,inputS,addTapeS),inputS,addTapeS)
  ensures isTransitionsDeterministic(fromDTMtoNDTM(delta,inputS,addTapeS),inputS,addTapeS)
{
  aDTMisAValidNDTM'(delta,inputS,addTapeS,delta.Keys);
}

lemma aDTMisAValidNDTM'(delta:DeterministicTransitions, inputS:InputSymbols, addTapeS:AdditionalTapeSymbols, keys:set<Key>)
  requires isTapeSymbolsValid(inputS, addTapeS)
  requires isDeterministicTransitionsValid(delta, inputS, addTapeS)
  requires keys <= delta.Keys
  ensures var delta' := fromDTMtoNDTM'(delta, inputS, addTapeS, keys);
          isTransitionsValid(delta', inputS, addTapeS) && 
          isTransitionsDeterministic(delta', inputS, addTapeS)
  decreases keys
{
  var delta' := fromDTMtoNDTM'(delta, inputS, addTapeS, keys);
  if |keys| == 0 {
  } else {
    var s :| s in keys;
    var rest := keys - {s};
    aDTMisAValidNDTM'(delta, inputS, addTapeS, rest);
    
  }
}
lemma aDeterminitiscNDTMisAValidDTM' (delta:Transitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols)
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isTransitionsValid(delta,inputS,addTapeS)
  requires isTransitionsDeterministic(delta,inputS,addTapeS)
  ensures  isDeterministicTransitionsValid(fromNDTMtoDTM(delta,inputS,addTapeS),inputS,addTapeS)
{

}
lemma aDeterminitiscNDTMisAValidDTM'' (delta:Transitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,keys:set<Key>)
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isTransitionsValid(delta,inputS,addTapeS)
  requires isTransitionsDeterministic(delta,inputS,addTapeS)
  requires keys<=delta.Keys
  ensures  isDeterministicTransitionsValid(fromNDTMtoDTM(delta,inputS,addTapeS),inputS,addTapeS)
  ensures var delta' := fromNDTMtoDTM'(delta, inputS, addTapeS, keys);
          isDeterministicTransitionsValid(delta', inputS, addTapeS) 
  decreases keys
{
  if |keys| != 0 {
    var s :| s in keys;
    aDeterminitiscNDTMisAValidDTM''(delta, inputS, addTapeS, keys - {s});
  }
}
lemma fromDTMtoNDTMEquivalence (delta:DeterministicTransitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols)
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isDeterministicTransitionsValid(delta,inputS,addTapeS)
  ensures var delta':=fromDTMtoNDTM(delta,inputS,addTapeS);
  isTransitionsValid(delta',inputS,addTapeS) && isTransitionsDeterministic(delta',inputS,addTapeS) && fromNDTMtoDTM(delta',inputS,addTapeS)==delta
{

}
lemma fromNDTMtoDTMEquivalence (delta:Transitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols)
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isTransitionsValid(delta,inputS,addTapeS)
  requires isTransitionsDeterministic(delta,inputS,addTapeS)
  ensures var delta':=fromNDTMtoDTM(delta,inputS,addTapeS);
  isDeterministicTransitionsValid(delta',inputS,addTapeS)  && fromDTMtoNDTM(delta',inputS,addTapeS)==delta
{

}
function applyTransitionDTM(config : Configuration, delta : DeterministicTransitions) : Option<Configuration>
{
    match config 
        case Configuration (s, tape,head) =>   if Key(s,tape(head)) in delta.Keys then 
                                                    match delta[Key(s,tape(head))]
                                                        case Action(state,symbol,direction) => 
                                                            match direction
                                                                case Left => Some(moveLeft(Configuration(state,changeSymbol(tape,head,symbol),head)))
                                                                case Right => Some(moveRight(Configuration(state,changeSymbol(tape,head,symbol),head)))
                                                else None
                      

}
ghost predicate isThereAClosedTransitionInNStepsForDTM(delta:DeterministicTransitions,inputS:InputSymbols ,addTapeS:AdditionalTapeSymbols, conf1:Configuration, conf2:Configuration, n:nat) // functii de tranzitii
    requires isTapeSymbolsValid(inputS,addTapeS)
    requires isDeterministicTransitionsValid(delta,inputS,addTapeS)
    decreases n
{
  if n==0 then conf1==conf2
    else  
  exists conf':Configuration:: applyTransitionDTM(conf1,delta)==Some(conf') && isThereAClosedTransitionInNStepsForDTM(delta,inputS,addTapeS,conf',conf2,n-1) 
}

lemma ClosedTransitionEquivalence (delta:DeterministicTransitions, inputS:InputSymbols, addTapeS:AdditionalTapeSymbols, conf1:Configuration, conf2:Configuration, n:nat)
  requires isTapeSymbolsValid(inputS, addTapeS)
  requires isDeterministicTransitionsValid(delta, inputS, addTapeS)
  requires isThereAClosedTransitionInNStepsForDTM(delta, inputS, addTapeS, conf1, conf2, n)
  ensures var delta' := fromDTMtoNDTM(delta, inputS, addTapeS);
          isThereAClosedTransitionInNSteps(delta', conf1, conf2, n)
  decreases n
{
  aDTMisAValidNDTM(delta,inputS,addTapeS);
  var delta' := fromDTMtoNDTM(delta, inputS, addTapeS);
  
  if n == 0 {
  } else {
    var conf_next :| applyTransitionDTM(conf1, delta) == Some(conf_next) && 
                     isThereAClosedTransitionInNStepsForDTM(delta, inputS, addTapeS, conf_next, conf2, n-1);
    
    var key := Key(conf1.s, conf1.tape(conf1.head));
    assert isTransitionsDeterministic(delta',inputS,addTapeS);
    assert forall q0:State,s0:Symbol :: Key(q0,s0) in delta.Keys ==> |delta'[Key(q0,s0)]|==1;
    assert  forall k:Key :: k in delta.Keys ==> (exists q0:State,s0:Symbol :: k==Key(q0,s0) && |delta'[Key(q0,s0)]|==1);
    assert forall k:Key:: k in delta.Keys ==> |delta'[k]|==1;
    assert isPozInTransitions(conf1, delta', 0);
    assert applyTransition(conf1, delta', 0) == Some(conf_next);
    
    ClosedTransitionEquivalence(delta, inputS, addTapeS, conf_next, conf2, n-1);
    
    assert exists c', poz:nat :: isPozInTransitions(conf1, delta', poz) && 
                                applyTransition(conf1, delta', poz) == Some(c') && 
                                isThereAClosedTransitionInNSteps(delta', c', conf2, n-1);
  }
}
lemma thereIsOnlyOnePathToACLosedTransitions(delta:DeterministicTransitions, inputS:InputSymbols, addTapeS:AdditionalTapeSymbols, conf1:Configuration, conf2:Configuration)
  requires isTapeSymbolsValid(inputS, addTapeS)
  requires isDeterministicTransitionsValid(delta, inputS, addTapeS)
  requires isThereAClosedTransitionDTM(delta,inputS,addTapeS, conf1, conf2)
  ensures isThereAClosedTransition(fromDTMtoNDTM(delta, inputS, addTapeS), conf1, conf2)
{
  var delta' := fromDTMtoNDTM(delta, inputS, addTapeS);
  
  var n :| isThereAClosedTransitionInNStepsForDTM(delta,inputS,addTapeS,conf1, conf2, n);
  assert isThereAClosedTransitionInNStepsForDTM(delta,inputS,addTapeS,conf1, conf2, n);
  ClosedTransitionEquivalence(delta, inputS, addTapeS, conf1, conf2, n);
}


lemma EquivalentSteps(delta:Transitions, delta':DeterministicTransitions, inputS:InputSymbols, addTapeS:AdditionalTapeSymbols, conf1:Configuration, conf2:Configuration, n:nat)
  requires isTapeSymbolsValid(inputS, addTapeS)
  requires isTransitionsValid(delta, inputS, addTapeS)
  requires isTransitionsDeterministic(delta, inputS, addTapeS)
  requires delta' == fromNDTMtoDTM(delta, inputS, addTapeS)
  requires isThereAClosedTransitionInNStepsForDTM(delta', inputS, addTapeS, conf1, conf2, n)
  ensures isThereAClosedTransitionInNSteps(delta, conf1, conf2, n)
  decreases n
{
  if n > 0 {
     var conf_next :| applyTransitionDTM(conf1, delta') == Some(conf_next) && 
                      isThereAClosedTransitionInNStepsForDTM(delta', inputS, addTapeS, conf_next, conf2, n-1);
     
  
     assert isPozInTransitions(conf1, delta, 0);
     assert applyTransition(conf1, delta, 0) == Some(conf_next);
     
     EquivalentSteps(delta, delta', inputS, addTapeS, conf_next, conf2, n-1);
  }
}

ghost predicate isThereAClosedTransitionDTM(delta:DeterministicTransitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,conf1:Configuration, conf2:Configuration)
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isDeterministicTransitionsValid(delta,inputS,addTapeS)
{
  exists n:nat:: isThereAClosedTransitionInNStepsForDTM(delta,inputS,addTapeS, conf1, conf2, n)
}

ghost predicate isThereAClosedTransitionInPolynomialTimeDTM(delta:DeterministicTransitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols, conf1:Configuration,conf2:Configuration,m:int)
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isDeterministicTransitionsValid(delta,inputS,addTapeS)
{
  exists n:nat:: isThereAClosedTransitionInNStepsForDTM(delta,inputS,addTapeS, conf1, conf2, n) && isPolynomial(n,m)  
}

lemma PolynomialClosedTransitionEquivalence (delta:DeterministicTransitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols, conf1:Configuration,conf2:Configuration,m:int)
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isDeterministicTransitionsValid(delta,inputS,addTapeS)
  requires  isThereAClosedTransitionInPolynomialTimeDTM(delta,inputS,addTapeS,conf1,conf2,m)
  ensures var delta':=fromDTMtoNDTM(delta,inputS,addTapeS);
  isTransitionsValid(delta',inputS,addTapeS) && 
  isThereAClosedTransitionInPolynomialTime(delta',conf1,conf2,m)
{
  
  assert isThereAClosedTransitionInPolynomialTimeDTM(delta,inputS,addTapeS,conf1,conf2,m);
  var n:|isThereAClosedTransitionInNStepsForDTM(delta,inputS,addTapeS, conf1, conf2, n) && isPolynomial(n,m);
  ClosedTransitionEquivalence(delta,inputS,addTapeS,conf1,conf2,n);
}
ghost predicate isAcceptedInDTM(delta : DeterministicTransitions, q0:State,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,input:seq<string>)
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isDeterministicTransitionsValid(delta,inputS,addTapeS)
  requires isInputValid(input,inputS)
{
  exists conf:Configuration :: isConfAccepted(conf) && isThereAClosedTransitionDTM(delta,inputS,addTapeS,initialConfiguration(input,q0,inputS),conf)
  
}

lemma AcceptedInDTMisAcceptedInTM (delta : DeterministicTransitions, q0:State,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,input:seq<string>)
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isDeterministicTransitionsValid(delta,inputS,addTapeS)
  requires isInputValid(input,inputS)
  requires isAcceptedInDTM(delta,q0,inputS,addTapeS,input)
  ensures var delta':=fromDTMtoNDTM(delta,inputS,addTapeS);
  isAcceptedInTM(delta',q0,inputS,addTapeS,input)
{
  assert isAcceptedInDTM(delta,q0,inputS,addTapeS,input);
  var conf:|isConfAccepted(conf) && isThereAClosedTransitionDTM(delta,inputS,addTapeS,initialConfiguration(input,q0,inputS),conf);
  thereIsOnlyOnePathToACLosedTransitions(delta,inputS,addTapeS,initialConfiguration(input,q0,inputS),conf);
}

ghost predicate isRejectedInDTM(delta : DeterministicTransitions, q0:State,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,input:seq<string>)
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isDeterministicTransitionsValid(delta,inputS,addTapeS)
  requires isInputValid(input,inputS)
{
  exists conf:Configuration :: isConfRejected(conf) && isThereAClosedTransitionDTM(delta,inputS,addTapeS,initialConfiguration(input,q0,inputS),conf)
  
}


lemma RejectedInDTMisRejectedInTM (delta : DeterministicTransitions, q0:State,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,input:seq<string>)
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isDeterministicTransitionsValid(delta,inputS,addTapeS)
  requires isInputValid(input,inputS)
  requires isRejectedInDTM(delta,q0,inputS,addTapeS,input)
  ensures var delta':=fromDTMtoNDTM(delta,inputS,addTapeS);
    isRejectedInTM(delta',q0,inputS,addTapeS,input)
{
  assert isRejectedInDTM(delta,q0,inputS,addTapeS,input);
  var conf:|isConfRejected(conf) && isThereAClosedTransitionDTM(delta,inputS,addTapeS,initialConfiguration(input,q0,inputS),conf);
  thereIsOnlyOnePathToACLosedTransitions(delta,inputS,addTapeS,initialConfiguration(input,q0,inputS),conf);
}
ghost predicate haltsInTM(delta : Transitions, q0:State,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,input:seq<string>)
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isTransitionsValid(delta,inputS,addTapeS)
  requires isInputValid(input,inputS)
{
  isRejectedInTM(delta,q0,inputS,addTapeS,input) || isAcceptedInTM(delta,q0,inputS,addTapeS,input)
}
ghost predicate haltsInDTM(delta : DeterministicTransitions, q0:State,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,input:seq<string>)
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isDeterministicTransitionsValid(delta,inputS,addTapeS)
  requires isInputValid(input,inputS)
{
  isRejectedInDTM(delta,q0,inputS,addTapeS,input) || isAcceptedInDTM(delta,q0,inputS,addTapeS,input)
}
ghost function beginDTM (delta:DeterministicTransitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,q0:State,input:seq<string>): Configuration
    requires isTapeSymbolsValid(inputS,addTapeS)
    requires isDeterministicTransitionsValid(delta,inputS,addTapeS)
    requires isInputValid(input,inputS)
    requires haltsInDTM(delta,q0,inputS,addTapeS,input)
{
   simulateDTM(delta,inputS,addTapeS,initialConfiguration(input,q0,inputS))
}
ghost predicate canAStateReachAFinalStateDTM(delta : DeterministicTransitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,conf1:Configuration)
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isDeterministicTransitionsValid(delta,inputS,addTapeS)
{
  exists conf:Configuration :: ( isConfAccepted(conf) || isConfRejected(conf))  && isThereAClosedTransitionDTM(delta,inputS,addTapeS,conf1,conf)

}
ghost predicate canAStateReachAFinalStateInNStepsDTM(delta : DeterministicTransitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,conf1:Configuration,n:nat)
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isDeterministicTransitionsValid(delta,inputS,addTapeS)
{
  exists conf:Configuration :: ( isConfAccepted(conf) || isConfRejected(conf))  && isThereAClosedTransitionInNStepsForDTM(delta,inputS,addTapeS,conf1,conf,n)
}

ghost predicate canAnInputReachAFinalStateDTM(delta:DeterministicTransitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,q0:State,input:seq<string>)
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isInputValid(input,inputS)
  requires isDeterministicTransitionsValid(delta,inputS,addTapeS)
{
  var conf1:=initialConfiguration(input,q0,inputS);
    canAStateReachAFinalStateDTM(delta,inputS,addTapeS,conf1)
}
lemma reachFinalStateEquivalence (delta : DeterministicTransitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,conf1:Configuration)
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isDeterministicTransitionsValid(delta,inputS,addTapeS)
  requires canAStateReachAFinalStateDTM(delta,inputS,addTapeS,conf1)
  ensures  var delta':=fromDTMtoNDTM(delta,inputS,addTapeS);
  canAStateReachAFinalState(delta',inputS,addTapeS,conf1)
{
  assert exists conf:Configuration :: ( isConfAccepted(conf) || isConfRejected(conf))  && isThereAClosedTransitionDTM(delta,inputS,addTapeS,conf1,conf);
  var conf:|( isConfAccepted(conf) || isConfRejected(conf))  && isThereAClosedTransitionDTM(delta,inputS,addTapeS,conf1,conf);
  thereIsOnlyOnePathToACLosedTransitions(delta,inputS,addTapeS,conf1,conf);
}

ghost function simulateDTM(delta:DeterministicTransitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,conf:Configuration): Configuration
    requires isTapeSymbolsValid(inputS,addTapeS)
    requires isDeterministicTransitionsValid(delta,inputS,addTapeS)
    requires canAStateReachAFinalStateDTM(delta,inputS,addTapeS,conf)
{
    assert canAStateReachAFinalStateDTM(delta,inputS,addTapeS,conf);
    var conf1:| ( isConfAccepted(conf1) || isConfRejected(conf1))  && isThereAClosedTransitionDTM(delta,inputS,addTapeS,conf,conf1);
    assert isThereAClosedTransitionDTM(delta,inputS,addTapeS,conf,conf1);
    assert exists n:nat::isThereAClosedTransitionInNStepsForDTM(delta,inputS,addTapeS,conf,conf1,n);
    var n:|isThereAClosedTransitionInNStepsForDTM(delta,inputS,addTapeS,conf,conf1,n);
    assert ( isConfAccepted(conf1) || isConfRejected(conf1))  && isThereAClosedTransitionInNStepsForDTM(delta,inputS,addTapeS,conf,conf1,n);
    assert canAStateReachAFinalStateInNStepsDTM(delta,inputS,addTapeS,conf,n);
    simulateDTM'(delta,inputS,addTapeS,conf,n)
}
ghost function simulateDTM'(delta:DeterministicTransitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,conf:Configuration, n:nat): Configuration
    requires isTapeSymbolsValid(inputS,addTapeS)
    requires isDeterministicTransitionsValid(delta,inputS,addTapeS)
    requires canAStateReachAFinalStateInNStepsDTM(delta,inputS,addTapeS,conf,n)
    decreases n
{
    match conf
        case Configuration(q,tape,head)    => match q
                                            case State(q,c) => match c 
                                                                case Some(_) => conf
                                                                case None =>match applyTransitionDTM(conf,delta)
                                                                            case Some(conf')=>
                                                                                simulateDTM'(delta,inputS,addTapeS,conf',n-1) // need to prove termination                                                                                                                                                                                       
}


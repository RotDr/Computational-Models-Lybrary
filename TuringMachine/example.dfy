include "DTM.dfy"

function getInputOfN (n:nat):seq<string>
  requires n>=0
  decreases n
{
  if n==0 then 
    []
  else
    ["1"]+getInputOfN(n-1)
}
predicate isInputCorrect (input:seq<string>)
  ensures isInputCorrect(input) ==> forall n:nat:: n<|input| ==> input[n]=="1"
  decreases input 
{
 if input==[] then true
 else 
    input[0]=="1" && isInputCorrect(input[1..])
}
function finalStateForInput (input:seq<string>) :State
{
  if |input|%2==0 then 
    State("qAcc", Some(Accept))
  else 
    State("qRej", Some(Reject))

}
function finalTapeForExample() : iseq<Symbol>
{
    i =>
        Blank
}
lemma TraceExecution(
  delta: DeterministicTransitions,
  inputS: InputSymbols,
  addTapeS: AdditionalTapeSymbols,
  current_conf: Configuration,
  n: nat
) returns (next_conf: Configuration)
  requires isTapeSymbolsValid(inputS, addTapeS)
  requires isDeterministicTransitionsValid(delta, inputS, addTapeS)
  requires {Key(State("q0", None), NonBlankSymbol("1")), Key(State("q1", None), NonBlankSymbol("1"))} <= delta.Keys
  requires delta[Key(State("q0", None), NonBlankSymbol("1"))] == Action(State("q1", None), Blank, Right)
  requires delta[Key(State("q1", None), NonBlankSymbol("1"))] == Action(State("q0", None), Blank, Right)
  requires current_conf.s == State("q0", None) || current_conf.s == State("q1", None)
  requires forall i :: current_conf.head <= i < current_conf.head + n ==> current_conf.tape(i) == NonBlankSymbol("1")
  requires current_conf.tape(current_conf.head + n) == Blank
  decreases n
  ensures next_conf.head == current_conf.head + n
  ensures next_conf.tape(next_conf.head) == Blank
  ensures next_conf.s == State("q0", None) || next_conf.s == State("q1", None)
  ensures isThereAClosedTransitionInNStepsForDTM(delta, inputS, addTapeS, current_conf, next_conf, n)
{
  if n == 0 {
    next_conf := current_conf;
  } else {
    match applyTransitionDTM(current_conf, delta)
      case Some(step_conf) => {
        next_conf := TraceExecution(delta, inputS, addTapeS, step_conf, n - 1);
      }
      case None => { }
  }
}

lemma CorrectInputHalts(
  delta: DeterministicTransitions, 
  inputS: InputSymbols, 
  addTapeS: AdditionalTapeSymbols, 
  q0: State, 
  q1: State, 
  qRej: State, 
  qAcc: State,
  one: Symbol, 
  input: seq<string>
)
  requires isInputCorrect(input)
  requires |input| >= 1
  requires one == NonBlankSymbol("1")
  requires inputS == {one}
  requires addTapeS == {Blank}
  requires isTapeSymbolsValid(inputS, addTapeS)
  requires isInputValid(input, inputS)
  requires isDeterministicTransitionsValid(delta, inputS, addTapeS)
  requires q0 == State("q0", None)
  requires q1 == State("q1", None)
  requires qRej == State("qRej", Some(Reject))
  requires qAcc == State("qAcc", Some(Accept))
  requires {Key(q0, one), Key(q1, one), Key(q1, Blank), Key(q0, Blank)} <= delta.Keys
  requires delta[Key(q0, one)] == Action(q1, Blank, Right)
  requires delta[Key(q1, one)] == Action(q0, Blank, Right)
  requires delta[Key(q1, Blank)] == Action(qRej, Blank, Right)
  requires delta[Key(q0, Blank)] == Action(qAcc, Blank, Right)
  ensures haltsInDTM(delta, q0, inputS, addTapeS, input)
{
  var init_config := initialConfiguration(input, q0, inputS);
  var steps := |input|;

  var mid_config := TraceExecution(delta, inputS, addTapeS, init_config, steps);
  
  match applyTransitionDTM(mid_config, delta)
    case Some(halt_config) => {
      LinkTransitions(delta, inputS, addTapeS, init_config, mid_config, halt_config, steps);

      assert isThereAClosedTransitionInNStepsForDTM(delta, inputS, addTapeS, init_config, halt_config, steps + 1);
      assert isThereAClosedTransitionDTM(delta,inputS,addTapeS,init_config,halt_config);
      assert haltsInDTM(delta, q0, inputS, addTapeS, input);
    }
}

method Main()
{
  var q0:=State("q0",None);
  var q1:=State("q1",None);
  var qAcc:=State("qAcc",Some(Accept));
  var qRej:=State("qRej",Some(Reject));
  var one:=NonBlankSymbol("1");
  var delta:= map[
    Key(q0,one) :=[Action(q1,Blank,Right)],
    Key(q1,one) := [Action(q0,Blank,Right)],
    Key(q0,Blank) := [Action(qAcc,Blank,Right)],
    Key(q1,Blank) := [Action(qRej,Blank,Right)]
  ];
  assert one==NonBlankSymbol("1");
  var input:=["1","1","1","1"];
  var inputS:={one};
  var addTapeS:={Blank};

  assert isTapeSymbolsValid(inputS, addTapeS);
  assert isInputValid(input, inputS);
  assert isTransitionsValid(delta, inputS, addTapeS);
  assert isTransitionsDeterministic(delta, inputS, addTapeS);
  
  var deltaDTM := fromNDTMtoDTM(delta, inputS, addTapeS);
  CorrectInputHalts(deltaDTM, inputS, addTapeS, q0, q1, qRej,qAcc,one,input);
  assert haltsInDTM(deltaDTM, q0, inputS, addTapeS, input);
  var finalConfig := beginDTM(deltaDTM, inputS, addTapeS, q0, input);
}
datatype Symbol = NonBlankSymbol (s : string) | Blank 

type InputSymbols = set<Symbol>

ghost predicate isInputValid (input:seq<string>,inputSymbols:InputSymbols)
{
  forall i:string :: (i in input) ==> (NonBlankSymbol(i) in inputSymbols)
}

type AdditionalTapeSymbols = set<Symbol> // Blank e mereu acelasi indiferent de tm

ghost predicate isTapeSymbolsValid (inps:InputSymbols,ats:AdditionalTapeSymbols)
{
    inps*ats=={} && Blank in ats
}

type iseq<T> = int -> T

type Tape = iseq<Symbol>

function moveLeft(con:Configuration) : Configuration
{
  match con 
    case Configuration(s,tape,head) => Configuration(s,tape,head-1)
}

function moveRight(con : Configuration) : Configuration
{
  match con 
    case Configuration(s,tape,head) => Configuration(s,tape,head+1)
}

datatype Conclusion = Accept | Reject 
datatype State = NormalState (s:string) | FinalState(s:string,conclusion:Conclusion)



datatype Configuration = Configuration(s : State, tape : iseq<Symbol>,head:int)

datatype Key = Key(state : State, symbol : Symbol)

datatype Direction = Left | Right
 
datatype Action = Action(state : State, symbol : Symbol, direction : Direction)
 
type Transitions = map<Key, Action>
ghost predicate isTransitionsValid(delta:Transitions,inps:InputSymbols,adts:AdditionalTapeSymbols)
  requires isTapeSymbolsValid(inps,adts)
{
  forall q0:State,s0:Symbol :: Key(q0,s0) in delta.Keys ==> ((s0 in inps+adts) && match delta[Key(q0,s0)]
                                                                                      case Action(_,s1,_) => s1 in inps+adts)
}
datatype Option<T> = Some(t:T) |None

function applyTransition(config : Configuration, delta : Transitions) : Option<Configuration>
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
function changeSymbol(tape: Tape, head:int,newSymbol:Symbol) : Tape
{
    i =>
        if i!=head then tape(i)
        else newSymbol
}
function initialTape(input : seq<string>) : iseq<Symbol>
{
    i =>
        if 0<=i<|input|  then NonBlankSymbol(input[i])
        else Blank
}

function initialConfiguration (input: seq<string>, q:State, inputS:InputSymbols)  :Configuration       // avem nevoie de o stare initiala
  requires isInputValid(input,inputS)
{
    Configuration(q,initialTape(input),0)
}
method runTM(delta : Transitions, input : seq<string>, q0:State,inputS:InputSymbols,AddTapeS:AdditionalTapeSymbols) returns (con:Option<Configuration>) // trebuie o stare initiala
  decreases *
  requires isTransitionsValid(delta,inputS,AddTapeS)
{
    var config:=initialConfiguration(input,q0,inputS);
    var m:=runTM'(delta,config);
    return m;
}
method runTM'(delta:Transitions,config:Configuration) returns (con: Option<Configuration>)
    decreases *
{
    match config
        case Configuration(q,tape,head)    => match q
                                            case FinalState(_,finale) => return Some(config);
                                            case NormalState(q0) =>{ 
                                                var conf:=applyTransition(config,delta);
                                                match conf 
                                                    case Some(c) =>{
                                                     var r:=runTM'(delta,c);
                                                      return r;
                                                    }
                                                    case None => return None;
                                            }
}

ghost predicate isThereAClosedTransitionInNSteps(delta:Transitions, conf1:Configuration, conf2:Configuration, n:nat)
    decreases n
{
  (n!=0) && (conf1==conf2 || (exists conf':: applyTransition(conf1,delta)==Some(conf') && isThereAClosedTransitionInNSteps(delta,conf',conf2,n-1))) // problema 1 LOOPING problema 2 nu se duce in directia buna))
}

ghost predicate isThereAClosedTransition(delta:Transitions, conf1:Configuration, conf2:Configuration)
{
  exists n:nat:: isThereAClosedTransitionInNSteps(delta, conf1, conf2, n)
}
type Language=set<seq<string>>
ghost predicate isConfAccepted(conf:Configuration)
{
    match conf 
    case Configuration(q,_,_) => match q
                                    case FinalState(_,c) => c==Accept
                                    case NormalState(_) => false
}
ghost predicate isConfRejected(conf:Configuration)
{
  match conf 
    case Configuration(q,_,_) => match q
                                    case FinalState(_,c) => c==Reject
                                    case NormalState(_) => false
}
ghost predicate isAcceptedInTM (delta : Transitions, q0:State,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,input:seq<string>)
  requires isTransitionsValid(delta,inputS,addTapeS)
{
  exists conf:Configuration :: isConfAccepted(conf) && isThereAClosedTransition(delta,initialConfiguration(input,q0,inputS),conf)

} 
ghost predicate isRejectedInTM (delta : Transitions, q0:State,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,input:seq<string>)
  requires isTransitionsValid(delta,inputS,addTapeS)
{
  exists conf:Configuration :: isConfRejected(conf) && isThereAClosedTransition(delta,initialConfiguration(input,q0,inputS),conf)

} 
ghost predicate isLanguageAcceptedInTM (delta:Transitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,q0:State,lang:Language)
    requires isTransitionsValid(delta,inputS,addTapeS)
{
    forall input:seq<string> :: (input in lang) <==> isAcceptedInTM(delta,q0,inputS,addTapeS,input)
}
ghost predicate isTMADecider (delta:Transitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,q0:State)
requires isTransitionsValid(delta,inputS,addTapeS)
{
  forall input:seq<string> :: (isAcceptedInTM(delta,q0,inputS,addTapeS,input) || isRejectedInTM(delta,q0,inputS,addTapeS,input))
}

ghost predicate isLanguageDecidable (lang:Language)
{
  exists delta:Transitions,q0:State,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols :: isTMADecider(delta,inputS,addTapeS,q0) && isLanguageAcceptedInTM(delta,inputS,addTapeS,q0,lang)
}
type reduction = seq<string>-> seq<string> //toate functiile sunt conputable by default aici

ghost predicate isReductionBetweenLanguages(A:Language,B:Language,r:reduction)
  requires isLanguageDecidable(A) && isLanguageDecidable(B)
{
  forall input:seq<string> :: (input in A) <==> (r(input) in B) 
}
function languageFromTM (delta:Transitions,q0:State,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols) : Language

method Main()
  decreases *
{
  var q0:=NormalState("q0");
  var q1:=NormalState("q1");
  var qAcc:=FinalState("qAcc",Accept);
  var qRej:=FinalState("qRej",Reject);
  var one:=NonBlankSymbol("1");
  var delta:= map[
    Key(q0,one) := Action(q1,Blank,Right),
    Key(q1,one) := Action(q0,Blank,Right),
    Key(q0,Blank) := Action(qAcc,Blank,Right),
    Key(q1,Blank) := Action(qRej,Blank,Right)
  ];
  assert one==NonBlankSymbol("1");
  var input:=["1","1","1","1","1"];
  print input;
  print "\n";
  var config:=runTM(delta,input,q0);
  match config
    case Some (c)=> {
      match c
        case Configuration(q,tape,head) => 
        {
          print q;
          print "\n";
          print head;
          print "\n";
          print tape(2);
          print tape(head);
        }
    }
    case None =>
    {
      print "failed";
    }
  // runTM
  // print tape
}
// defineste un limbaj si limbaj decidabil in dafny
// inchidere tranzition
// reduceable
// codare a unui limbaj np complete
// 
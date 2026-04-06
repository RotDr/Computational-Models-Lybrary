datatype Symbol = NonBlankSymbol (s : string) | Blank 

type InputSymbols = set<Symbol>

ghost predicate isInputValid (input:seq<string>,inputSymbols:InputSymbols)
{
  forall i:string :: (i in input) ==> (NonBlankSymbol(i) in inputSymbols)
}

type AdditionalTapeSymbols = set<Symbol> // Blank e mereu acelasi indiferent de tm

ghost predicate isTapeSymbolsValid (inputS:InputSymbols,ats:AdditionalTapeSymbols)
{
    inputS*ats=={} && Blank in ats
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
datatype State = State (s:string, c:Option<Conclusion>)



datatype Configuration = Configuration(s : State, tape : iseq<Symbol>,head:int)

datatype Key = Key(state : State, symbol : Symbol)

datatype Direction = Left | Right
 
datatype Action = Action(state : State, symbol : Symbol, direction : Direction)
 
type Transitions = map<Key,seq<Action>> 
ghost predicate isTransitionsValid(delta:Transitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols)
  requires isTapeSymbolsValid(inputS,addTapeS)
{
  forall q0:State,s0:Symbol :: Key(q0,s0) in delta.Keys ==> ((s0 in inputS+addTapeS) && 
                                                              |delta[Key(q0,s0)]|>=1 &&
                                                            (forall i:Action:: i in delta[Key(q0,s0)] ==>
                                                                                                          match i 
                                                                                                            case Action(_,s1,_) => s1 in inputS+addTapeS))
}
datatype Option<T> = Some(t:T) |None
predicate isPozInTransitions(config : Configuration, delta : Transitions, poz:int)
{
  match config 
        case Configuration (s, tape,head) => if Key(s,tape(head)) in delta.Keys then 
                                                    0<=poz<|delta[Key(s,tape(head))]|
                                             else 
                                                true
}
function applyTransition(config : Configuration, delta : Transitions, poz:int) : Option<Configuration>
  requires isPozInTransitions(config, delta, poz)
{
    match config 
        case Configuration (s, tape,head) =>   if Key(s,tape(head)) in delta.Keys then 
                                                    match delta[Key(s,tape(head))][poz]
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


// predicat daca exista transitions sa faca transitions 
// lemma despre masina turing care sa arate ca pt numere impare exista un 
// functie functie predicat ghost si demonstrarite
// function simulateDTM (delta:Transitions,config:Configuration,inputS:InputSymbols,AddTapeS:AdditionalTapeSymbols): Option<Configuration>
//     requires isTapeSymbolsValid(inputS,AddTapeS)
//     requires isTransitionsValid(delta,inputS,AddTapeS)
//     requires isTransitionsDeterministic(delta,inputS,AddTapeS)
// {

// }
ghost predicate isThereAClosedTransitionInNSteps(delta:Transitions, conf1:Configuration, conf2:Configuration, n:nat) // functii de tranzitii
// definitia asta era flawed initial incat nu ia in considerare cazul particular de 0
    decreases n
{
  if n==0 then conf1==conf2
    else  
  exists conf',poz:nat::(isPozInTransitions(conf1,delta,poz)) && applyTransition(conf1,delta,poz)==Some(conf') && isThereAClosedTransitionInNSteps(delta,conf',conf2,n-1) // problema 1 LOOPING problema 2 nu se duce in directia buna))
}

ghost predicate isThereAClosedTransition(delta:Transitions,conf1:Configuration, conf2:Configuration)
{
  exists n:nat:: isThereAClosedTransitionInNSteps(delta, conf1, conf2, n)
}

function Pow(n:nat,m:nat) : nat
{
  if m==0 then 1
  else n*Pow(n,m-1)
}
ghost predicate isPolynomial (n:nat,m:int)
{
  exists x:nat ::Pow(n,x)<=m && Pow(n,x+1)>=m
}
ghost predicate isThereAClosedTransitionInPolynomialTime(delta:Transitions, conf1:Configuration,conf2:Configuration,m:int)
{
  exists n:nat:: isThereAClosedTransitionInNSteps(delta, conf1, conf2, n) && isPolynomial(n,m)  // de facut DTM equivalent 
}
type Language=set<seq<string>>
ghost predicate isConfAccepted(conf:Configuration)
{
    match conf 
    case Configuration(q,_,_) => match q
                                    case State(_,c) => match c 
                                                          case None => false
                                                          case Some(con) => con==Accept
                                  
}
ghost predicate isConfRejected(conf:Configuration)
{
    match conf 
    case Configuration(q,_,_) => match q
                                    case State(_,c) => match c 
                                                          case None => false
                                                          case Some(con) => con==Accept
}
ghost predicate canAStateReachAFinalState(delta : Transitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,conf1:Configuration)
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isTransitionsValid(delta,inputS,addTapeS)
{
  exists conf:Configuration :: ( isConfAccepted(conf) || isConfRejected(conf))  && isThereAClosedTransition(delta,conf1,conf)
}


ghost predicate isAcceptedInTM (delta : Transitions, q0:State,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,input:seq<string>)
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isTransitionsValid(delta,inputS,addTapeS)
  requires isInputValid(input,inputS)
{
  exists conf:Configuration :: isConfAccepted(conf) && isThereAClosedTransition(delta,initialConfiguration(input,q0,inputS),conf)
}

ghost predicate isAcceptedInTMInPolynomialTime(delta:Transitions,q0:State,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,input:seq<string>) 
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isTransitionsValid(delta,inputS,addTapeS)
  requires isInputValid(input,inputS)
{
  exists conf:Configuration :: isConfAccepted(conf) && isThereAClosedTransitionInPolynomialTime(delta,initialConfiguration(input,q0,inputS),conf,|input|)
} 


lemma AcceptedInTMInPolynomialTime(delta:Transitions,q0:State,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,input:seq<string>)
    requires isTapeSymbolsValid(inputS,addTapeS)
    requires isTransitionsValid(delta,inputS,addTapeS)
    requires isInputValid(input,inputS)
    requires isAcceptedInTMInPolynomialTime(delta,q0,inputS,addTapeS,input)
    ensures isAcceptedInTM(delta,q0,inputS,addTapeS,input)
{

}
ghost predicate isRejectedInTM (delta : Transitions, q0:State,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,input:seq<string>)
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isTransitionsValid(delta,inputS,addTapeS)
  requires isInputValid(input,inputS)
{
  exists conf:Configuration :: isConfRejected(conf) && isThereAClosedTransition(delta,initialConfiguration(input,q0,inputS),conf)

} 
ghost predicate isLanguageAcceptedInTM (delta:Transitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,q0:State,lang:Language)
    requires isTapeSymbolsValid(inputS,addTapeS)
    requires isTransitionsValid(delta,inputS,addTapeS)
{
    forall input:seq<string> :: (input in lang) <==> ( 
    isInputValid(input,inputS) 
    && 
    isAcceptedInTM(delta,q0,inputS,addTapeS,input))
}
ghost predicate isLanguageAcceptedInTMInPolynomialTime(delta:Transitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,q0:State,lang:Language)
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isTransitionsValid(delta,inputS,addTapeS)
{
  forall input:seq<string> :: (input in lang) <==> (
    isInputValid(input,inputS) 
    && 
    isAcceptedInTMInPolynomialTime(delta,q0,inputS,addTapeS,input))
}

lemma AcceptedInTMEquivalence (delta:Transitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,q0:State,lang:Language)
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isTransitionsValid(delta,inputS,addTapeS)
{

}


// ghost predicate isLanguageNPHard (A:Language)
//   requires isLanguageDecidable(A)
// {
//   forall B:Language :: isLanguageNPTIME1(B) ==> 
//   (exists r:reduction :: isReductionBetweenLanguages(B,A,r))  // INCOMPLET, nu cred ca pot face o functie, imi trebuie o lemma
// }
// type reduction = seq<string>-> seq<string> // ASTA ESTE UN MAPPING REDUCTION, NU POLYNOMIAL REDUCTION 

// ghost predicate isReductionBetweenLanguages(A:Language,B:Language,r:reduction)
//   requires isLanguageDecidable(A) && isLanguageDecidable(B)
// {
//   forall input:seq<string> :: (input in A) <==> (r(input) in B) 
// }


// defineste un limbaj si limbaj decidabil in dafny
// inchidere tranzition
// reduceable
// codare a unui limbaj np complete
//https://lucatrevisan.github.io/30540/notes-np4.pdf
// https://www.csd.uoc.gr/~hy380/slides/18-NPComplete.pdf
//https://people.clarkson.edu/~alexis/PCMI/Notes/lectureB07.pdf
// https://dl.acm.org/doi/epdf/10.1145/1806689.1806724
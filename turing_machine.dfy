datatype Symbol = NonBlankSymbol (s : string) | Blank 

const InputSymbols : set<string>

const AdditionalTapeSymbols : set<string>

//type iseq<T> = nat -> T

/*atatype Tape = Tape(left : iseq<Symbol>, current : Symbol, right : iseq<Symbol>)

function first<T>(s : iseq<T>) : T
{
  s(0)
}

function rest<T>(s : iseq<T>) : iseq<T>
{
  ((i : nat) => s(i + 1))
}

function cons<T>(t : T, s : iseq<T>) : iseq<T>
{
  ((i : nat) => if i == 0 then t else s(i - 1))
}
 
function moveLeft(tape : Tape) : Tape
{
  Tape(rest(tape.left), first(tape.left), cons(tape.current, tape.right))
}
 
function moveRight(tape : Tape) : Tape
{
  Tape(cons(tape.current, tape.left), first(tape.right), rest(tape.right))
}*/

type iseq<T> = int -> T

type Tape = iseq<Symbol>

function moveLeft(con:Configuration) : Configuration
{
  match con 
    case Configuration(s,tape,arrow) => Configuration(s,tape,arrow+1)
}

function moveRight(con : Configuration) : Configuration
{
  match con 
    case Configuration(s,tape,arrow) => Configuration(s,tape,arrow-1)
}

datatype Conclusion = Accept | Reject | Blocked  // blocked e cazul in care nu ai nicio tranzitie pe care o poate folosi masina turing intr-o configuratie
datatype State = NormalState (s:string) | FinalState(s:string,conclusion:Conclusion)



datatype Configuration = Configuration(s : State, tape : iseq<Symbol>,arrow:int)

datatype Key = Key(state : State, symbol : Symbol)

datatype Direction = Left | Right
 
datatype Action = Action(state : State, symbol : Symbol, direction : Direction)
 
type Transitions = map<Key, Action>

function applyTransition(config : Configuration, delta : Transitions) : Configuration
{
    match config 
        case Configuration (s, tape,arrow) =>   if Key(s,tape(arrow)) in delta.Keys then 
                                                    match delta[Key(s,tape(arrow))] 
                                                        case Action(state,symbol,direction) => 
                                                            match direction
                                                                case Left => moveLeft(Configuration(state,changeSymbol(tape,arrow,symbol),arrow))
                                                                case Right => moveRight(Configuration(state,changeSymbol(tape,arrow,symbol),arrow))
                                                else Configuration(FinalState("",Blocked),tape,arrow)

}
function changeSymbol(tape: Tape, arrow:int,newSymbol:Symbol) : Tape
{
    i =>
        if i!=arrow then tape(i)
        else newSymbol
}
function initialTape(input : seq<string>) : iseq<Symbol>
{
    i =>
        if 0<=i<|input|  then NonBlankSymbol(input[i])
        else Blank
}

function initialConfiguration (input: seq<string>, q:State)  :Configuration       // avem nevoie de o stare initiala
{
    Configuration(q,initialTape(input),0)
}
method runTM(delta : Transitions, input : seq<string>, q0:State) returns (c:Conclusion) // trebuie o stare initiala
  decreases *
{
    var config:=initialConfiguration(input,q0);
    var m:=runTM'(delta,config);
    return m;
}
method runTM'(delta:Transitions,config:Configuration) returns (c: Conclusion)
    decreases *
{
    match config
        case Configuration(q,tape,arrow)    => match q
                                            case FinalState(_,finale) => return finale;
                                            case NormalState(q0) =>{ 
                                                var m:=runTM'(delta,applyTransition(config,delta));
                                                return m;
                                            }
}   

method Main()
  decreases *
{
  // var delta : Transitions := ...
  // runTM
  // print tape
}


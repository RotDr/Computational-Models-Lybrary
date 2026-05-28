include "Lambda.dfy"

predicate isCorrectForBetaReduction(t:LambdaTerm)
{
    match t
                case Application(Lambda(_,_),_) => true
                case _ => false
}

function betaReduction(t:LambdaTerm) : LambdaTerm
    requires isCorrectForBetaReduction(t)
            
{
    match t 
        case Application(Lambda(x,t1),t2) => caSubstitution(t1,x,t2)
}

function numberOfPossibleReducations (t:LambdaTerm) :nat 
{
    match t 
        case Var(_) => 0
        case Lambda(_,t') => numberOfPossibleReducations(t')
        case Application(t1,t2) =>  if isCorrectForBetaReduction(t) then 1+numberOfPossibleReducations(t1)+numberOfPossibleReducations(t2)
                                    else numberOfPossibleReducations(t1)+numberOfPossibleReducations(t2)
}


function betaReductionStep(t:LambdaTerm,choice:nat) : LambdaTerm
    requires 0<numberOfPossibleReducations(t)
    requires choice<numberOfPossibleReducations(t)
{
    if isCorrectForBetaReduction(t) then 
        if choice==0 then
            betaReduction(t)
        else 
            match t
                case Application(t1,t2) => (
                    var n1:=numberOfPossibleReducations(t1);
                    if n1>=choice then
                        assert choice<=n1;
                        Application(betaReductionStep(t1,choice-1),t2)
                    else 
                        assert choice>n1;
                        assert choice<numberOfPossibleReducations(t);
                        assert numberOfPossibleReducations(t2)+n1+1==numberOfPossibleReducations(t);
                        Application(t1,betaReductionStep(t2,choice-n1-1))
                ) 
    else 
        match t
                case Lambda(x,t')=> Lambda(x,betaReductionStep(t',choice))
                case Application(t1,t2) => (
                    var n1:=numberOfPossibleReducations(t1);
                    if n1>choice then
                        Application(betaReductionStep(t1,choice),t2)
                    else 
                        assert choice>=n1;
                        assert choice<numberOfPossibleReducations(t);
                        assert numberOfPossibleReducations(t2)+n1==numberOfPossibleReducations(t);
                        Application(t1,betaReductionStep(t2,choice-n1))
                )

}

predicate betaReductionClosure (t1:LambdaTerm,t2:LambdaTerm)
{
    exists n:nat::n<numberOfPossibleReducations(t1) && betaReductionStep(t1,n)==t2
}


ghost predicate betaReducationInNSteps (t1:LambdaTerm,t2:LambdaTerm,n:nat)
    decreases n
{
    if n==0 then t1==t2 
    else
        exists t':LambdaTerm:: betaReductionClosure(t1,t')  && betaReducationInNSteps(t',t2,n-1)
}

ghost predicate betaReducationsClosure(t1:LambdaTerm,t2:LambdaTerm)
{
    exists n:nat:: betaReducationInNSteps(t1,t2,n)
}
// De a demonstra confluenta pe dabaz documentului de la waterloo https://student.cs.uwaterloo.ca/~cs442/W22/extras/c-r-thm-proof.pdf
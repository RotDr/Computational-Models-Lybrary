include "Substitutions.dfy"

function normalOrderStep(t:LambdaTerm) : Option<LambdaTerm> 
        requires var s1:=vars(t);
        allUnique(s1) 
{
    match t 
        case Var(x)=> None
        case Application(Lambda(x,t1),t') => Some(caSubstitution(t1,x,t'))
        case Application(t1,t2) => 
                                   ( match normalOrderStep(t1) 
                                        case None =>( match normalOrderStep(t2)
                                                        case None => None 
                                                        case Some(t2') => Some(Application(t1,t2')))
                                        
                                        case Some(t1')=> Some(Application(t1',t2)) 
                                   )      
        case Lambda(x,t') => (match normalOrderStep(t')
                                case  None => None
                               case Some(t2) => Some(Lambda(x,t2))
        )
        
}

lemma betaPreservesUniqueVars(t:LambdaTerm, t':LambdaTerm)
    requires allUnique(vars(t))
    requires normalOrderStep(t) == Some(t')
    ensures allUnique(vars(t'))
{

}

predicate normalOrderEndsInNSteps (t:LambdaTerm,n:nat)
    decreases n
{
    match normalOrderStep(t)
        case None=> n==0
        case Some(t') => n>0 && normalOrderEndsInNSteps(t',n-1)
}

ghost predicate normalOrderHalts(t:LambdaTerm)
{
    exists n:nat :: normalOrderEndsInNSteps(t,n)
}

ghost function normalOrder(t:LambdaTerm) : LambdaTerm
    requires normalOrderHalts(t)
     requires var s1:=vars(t);
        allUnique(s1) 
{
    var n:|normalOrderEndsInNSteps(t,n);
    normalOrder'(t,n)
}
function normalOrder'(t:LambdaTerm,n:nat) : LambdaTerm
    requires normalOrderEndsInNSteps(t,n)
    requires var s1:=vars(t);
        allUnique(s1) 
    decreases n

{
    if n==0 then 
        t
    else 
        var t':|Some(t')==normalOrderStep(t);
        normalOrder'(t',n-1)
}

lemma normalOrderStepsUnique(t:LambdaTerm, n:nat, m:nat)
    requires normalOrderEndsInNSteps(t,n)
    requires normalOrderEndsInNSteps(t,m)
    ensures n == m
    decreases n
{
    match normalOrderStep(t) {
        case None => {}
        case Some(t') =>
            betaPreservesUniqueVars(t, t');
            normalOrderStepsUnique(t', n-1, m-1);
    }
}

method Main()
{
    var x:=1;
    var testing:=Application(Lambda(x,Application(Var(x),Var(x))),Lambda(x,Application(Var(x),Var(x))));
    var result:=normalOrderStep(testing);
    print (result);
}
include "../BetaReduction.dfy"
include "MainLemmas/LemmaA5AndA6.dfy"
include "Helpers/HelperLemmasForA3.dfy"
include "MainLemmas/LemmaA7.dfy"


ghost predicate parallelReductionInNSteps(t1:LambdaTerm,t2:LambdaTerm,n:nat)
    decreases n
{
    if n==0 then alphaEquivalence(t1,t2)
    else 
    exists t':LambdaTerm:: parallelReduction(t1,t') && parallelReductionInNSteps(t',t2,n-1)
}

ghost predicate parallelReductionClosure(t1:LambdaTerm,t2:LambdaTerm)
{
    exists n:nat::parallelReductionInNSteps(t1,t2,n)
}

lemma parallelReductionClosureReflexive(t1:LambdaTerm)
    ensures parallelReductionClosure(t1,t1)
{
    EqualTermsAreAlphaEquilvalent(t1,t1);
    assert alphaEquivalence(t1,t1);
    assert parallelReductionInNSteps(t1,t1,0);
}
lemma ParClosurePrepend(a:LambdaTerm, b:LambdaTerm, c:LambdaTerm)   
    requires parallelReduction(a, b)
    requires parallelReductionClosure(b, c)
    ensures parallelReductionClosure(a, c)
{
    var n:nat :| parallelReductionInNSteps(b, c, n);
    assert parallelReductionInNSteps(a, c, n+1);     
}
lemma StripLemma(a:LambdaTerm,b:LambdaTerm,c:LambdaTerm,n:nat)
    requires parallelReduction(a, b)
    requires parallelReductionInNSteps(a, c, n)
    ensures exists d:LambdaTerm ::parallelReductionClosure(b, d) && parallelReduction(c, d)
    decreases n
{
    if n==0{

        assert alphaEquivalence(a,c);
        assert parallelReduction(a,b);
        EqualTermsAreAlphaEquilvalent(b,b);
        ParallelReductionAlphaInvariance(a,b,c,b);
        assert parallelReduction(b,b);
        assert parallelReduction(c,b);
        assert parallelReductionInNSteps(b,b,0);
        assert parallelReductionInNSteps(c,b,1);

    }
    else
    {
        var next_a :| parallelReduction(a, next_a) && parallelReductionInNSteps(next_a, c, n-1);
        DiamondLemma(a, b, next_a);                    
        var e :| parallelReduction(b, e) && parallelReduction(next_a, e);
        StripLemma(next_a, e, c, n-1);                  
        var d :| parallelReductionClosure(e, d) && parallelReduction(c, d);
        ParClosurePrepend(b, e, d);                    
        assert parallelReductionClosure(b, d) && parallelReduction(c, d);
    }
}

lemma ClosureDiamond(a:LambdaTerm, b:LambdaTerm, c:LambdaTerm, n:nat)
    requires parallelReductionInNSteps(a, b, n)
    requires parallelReductionClosure(a, c)
    ensures exists d:LambdaTerm :: parallelReductionClosure(b, d) && parallelReductionClosure(c, d)
    decreases n
{
    if (n==0)
    {
        assert alphaEquivalence(a, b);
        AlphaEquivSymmetric(a, b);                
        ParClosurePrepend(b, a, c);                
        parallelReductionClosureReflexive(c);     
        assert parallelReductionClosure(b, c) && parallelReductionClosure(c, c);
        
    }
    else
    {
        var a_next :| parallelReduction(a, a_next) && parallelReductionInNSteps(a_next, b, n-1);
        var m:nat :| parallelReductionInNSteps(a, c, m);
        StripLemma(a, a_next, c, m);                    
        var e :| parallelReductionClosure(a_next, e) && parallelReduction(c, e);
        ClosureDiamond(a_next, b, e, n-1);             
        var d :| parallelReductionClosure(b, d) && parallelReductionClosure(e, d);
        ParClosurePrepend(c, e, d);                
        assert parallelReductionClosure(b, d) && parallelReductionClosure(c, d);
    }
}


lemma ParallelClosureHasDiamond(a:LambdaTerm, b:LambdaTerm, c:LambdaTerm)
    requires parallelReductionClosure(a, b)
    requires parallelReductionClosure(a, c)
    ensures exists d:LambdaTerm :: parallelReductionClosure(b, d) && parallelReductionClosure(c, d)
{
    var m:nat :| parallelReductionInNSteps(a, b, m);
    ClosureDiamond(a, b, c, m);
}
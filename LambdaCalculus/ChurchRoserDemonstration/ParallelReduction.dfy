include "../AlphaEquivalence.dfy"



ghost predicate parallelReduction(t1:LambdaTerm, t2:LambdaTerm)
    decreases lHeight(t1)
{
    alphaEquivalence(t1, t2) || //rule 1 
    match t1
        case Application(t1a, t1b) =>
            (match t2
                case Application(t2a, t2b) =>
                    parallelReduction(t1a, t2a) && parallelReduction(t1b, t2b)
                case _ => false)
            ||
            (match t1a
                case Lambda(x, M) =>
                    exists M': LambdaTerm, N': LambdaTerm ::
                        (assert lHeight(M) < lHeight(t1); parallelReduction(M, M'))
                        && parallelReduction(t1b, N')
                        && alphaEquivalence(t2, caSubstitution(M', x, N'))   
                case _ => false)
        case Lambda(x, body1) =>
            exists r: LambdaTerm ::
                parallelReduction(body1, r) && alphaEquivalence(Lambda(x, r), t2)
        case _ => false
}

ghost predicate rule2(t1:LambdaTerm,t2:LambdaTerm) 
    ensures rule2(t1,t2) ==> parallelReduction(t1,t2)
{
    match t1 
        case Lambda(x, body1) =>
            exists r: LambdaTerm ::
                parallelReduction(body1, r) && alphaEquivalence(Lambda(x, r), t2)
        case _=> false
}
ghost predicate rule3(t1:LambdaTerm,t2:LambdaTerm)
    ensures rule3(t1,t2) ==> parallelReduction(t1,t2)
{
    match t1
        case Application(t1a, t1b) =>
            (match t2
                case Application(t2a, t2b) =>
                    parallelReduction(t1a, t2a) && parallelReduction(t1b, t2b)
                case _ => false)
        case _ => false
}
ghost predicate rule4(t1:LambdaTerm,t2:LambdaTerm)
    ensures rule4(t1,t2) ==> parallelReduction(t1,t2)
{
    match t1
        case Application(t1a, t1b) =>(match t1a
                                            case Lambda(x, M) =>
                                                exists M': LambdaTerm, N': LambdaTerm ::
                                                (assert lHeight(M) < lHeight(t1); parallelReduction(M, M'))
                                                && parallelReduction(t1b, N')
                                                && alphaEquivalence(t2, caSubstitution(M', x, N'))   
                                    case _ => false)
        case _=> false
}


lemma ParallelReductionIsReflexive (t:LambdaTerm)
    ensures parallelReduction(t,t)
{
    EqualTermsAreAlphaEquilvalent(t,t);
}


lemma ParallelReductionIsBasedOnFourRules(t1:LambdaTerm,t2:LambdaTerm)
    requires parallelReduction(t1,t2)
    ensures alphaEquivalence(t1,t2) || rule2(t1,t2) || rule3(t1,t2) || rule4(t1,t2)
{

}


lemma FourRulesDefineParallelReduction (t1:LambdaTerm,t2:LambdaTerm)
    requires alphaEquivalence(t1,t2) || rule2(t1,t2) || rule3(t1,t2) || rule4(t1,t2)
    ensures parallelReduction(t1,t2)
{

}



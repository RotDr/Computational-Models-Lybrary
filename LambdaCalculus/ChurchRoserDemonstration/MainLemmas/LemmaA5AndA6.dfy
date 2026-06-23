include "../ParallelReduction.dfy"
lemma LambdaParallelLemma (M:LambdaTerm,N:LambdaTerm,x:Id) // LEMMA A5
    requires parallelReduction(Lambda(x,M),N)
    ensures exists M': LambdaTerm :: parallelReduction(M, M') && alphaEquivalence(Lambda(x, M'), N)
{
    if alphaEquivalence(Lambda(x, M), N) {
        ParallelReductionIsReflexive(M);
    } 

}


lemma AlphaParallelLemma(M: LambdaTerm, N: LambdaTerm, L: LambdaTerm) // LEMMA A6

    requires parallelReduction(Application(M, N), L)
    ensures 
        (exists M': LambdaTerm, N': LambdaTerm :: 
            parallelReduction(M, M') && parallelReduction(N, N') && alphaEquivalence(Application(M', N'), L))
        ||
        (M.Lambda? && 
         exists P': LambdaTerm, N': LambdaTerm :: 
            parallelReduction(M.t, P') && parallelReduction(N, N') && alphaEquivalence(L, caSubstitution(P', M.x, N')))
{

    if alphaEquivalence(Application(M, N), L) {
        ParallelReductionIsReflexive(M);
        ParallelReductionIsReflexive(N);
        assert parallelReduction(M, M);
        assert parallelReduction(N, N);
        assert alphaEquivalence(Application(M, N), L);
    } 
    else {
            
        if rule3(Application(M,N),L) {
            match L 
                case Application(M',N') =>{
                    EqualTermsAreAlphaEquilvalent(Application(M', N'), L);
                    assert parallelReduction(M, M') && parallelReduction(N, N') && alphaEquivalence(Application(M', N'), L);
                }
        } 
    }
}
include "../ParallelReduction.dfy"
include "../../SubstitutionsAndSets.dfy"
include "../Helpers/HelperLemmasForA3.dfy"

lemma parallelReductionSubstitution(M:LambdaTerm,N:LambdaTerm,N':LambdaTerm,x:Id)
    requires parallelReduction(N,N')
    ensures parallelReduction(caSubstitution(M,x,N),caSubstitution(M,x,N'))
    decreases lHeight(M)
{
    match M 
        case Var(y) =>
        {
            getVarCaSubstitution(M,x,N);
            getVarCaSubstitution(M,x,N');
            if (y!=x)
            {
                assert caSubstitution(M,x,N)==M;
                assert caSubstitution(M,x,N')==M; 
                EqualTermsAreAlphaEquilvalent(caSubstitution(M,x,N),M);
                EqualTermsAreAlphaEquilvalent(M,caSubstitution(M,x,N'));
                AlphaEquivTransitive(caSubstitution(M,x,N),M,caSubstitution(M,x,N'));
                assert alphaEquivalence(caSubstitution(M,x,N),caSubstitution(M,x,N'));
            }
            else 
            {
                assert caSubstitution(M,x,N)==N;
                assert caSubstitution(M,x,N')==N'; 
                
                assert parallelReduction(N,N'); 
            }
        }
        case Application(P,Q) =>
        {
            var sub_P_N:=caSubstitution(P,x,N);
            var sub_P_N':=caSubstitution(P,x,N');
            var sub_Q_N:=caSubstitution(Q,x,N);
            var sub_Q_N':=caSubstitution(Q,x,N');
            SubstDistributesOverApp(P,Q,x,N);
            SubstDistributesOverApp(P,Q,x,N');

            var left_result:=Application(sub_P_N,sub_Q_N);
            var right_result:=Application(sub_P_N',sub_Q_N');

            assert alphaEquivalence(caSubstitution(M,x,N),Application(sub_P_N,sub_Q_N));
            assert alphaEquivalence(caSubstitution(M,x,N'),Application(sub_P_N',sub_Q_N'));
            AlphaEquivSymmetric(caSubstitution(M,x,N),Application(sub_P_N,sub_Q_N));
            AlphaEquivSymmetric(caSubstitution(M,x,N'),Application(sub_P_N',sub_Q_N'));

            parallelReductionSubstitution(P,N,N',x);
            parallelReductionSubstitution(Q,N,N',x);

            assert parallelReduction(sub_P_N,sub_P_N');
            assert parallelReduction(sub_Q_N,sub_Q_N');

            assert parallelReduction(left_result,right_result);
            assert alphaEquivalence(right_result,caSubstitution(M,x,N'));
            assert alphaEquivalence(left_result,caSubstitution(M,x,N));
            ParallelReductionAlphaInvariance(left_result,right_result,caSubstitution(M,x,N),caSubstitution(M,x,N'));

            assert parallelReduction(caSubstitution(M,x,N),caSubstitution(M,x,N'));
        }
        case Lambda(y,P) =>
        {
            if (y==x)
            {
                LambdaNullifiesSubstitution(P,x,N');
                LambdaNullifiesSubstitution(P,x,N);
                assert caSubstitution(M,x,N')==M;
                assert caSubstitution(M,x,N)==M;
                
                EqualTermsAreAlphaEquilvalent(M,M);

                assert alphaEquivalence(caSubstitution(M,x,N),caSubstitution(M,x,N'));
                assert parallelReduction(caSubstitution(M,x,N),caSubstitution(M,x,N')); 
            }
           else 
            {

                var M_sub_N := caSubstitution(M, x, N);
                var M_sub_N' := caSubstitution(M, x, N');

                if !(y in free(N)) && !(y in free(N'))
                {

                    var P_sub_N := caSubstitution(P, x, N);
                    var P_sub_N' := caSubstitution(P, x, N');

                    parallelReductionSubstitution(P, N, N', x);

                    var left_lambda := Lambda(y, P_sub_N);
                    var right_lambda := Lambda(y, P_sub_N');

                    assert parallelReduction(left_lambda, right_lambda) by {
                        assert parallelReduction(P_sub_N, P_sub_N'); 
                        EqualTermsAreAlphaEquilvalent(Lambda(y, P_sub_N'), right_lambda);
                        assert parallelReduction(P_sub_N, P_sub_N') && alphaEquivalence(Lambda(y, P_sub_N'), right_lambda);
                    }

                    assert alphaEquivalence(left_lambda, M_sub_N) by {
                        assert M == Lambda(y, P);
                        SubstPushesIntoSafeLambda(y, P, x, N);
                        AlphaEquivSymmetric(M_sub_N, left_lambda);
                    }

                    assert alphaEquivalence(right_lambda, M_sub_N') by {
                        assert M == Lambda(y, P);
                        SubstPushesIntoSafeLambda(y, P, x, N');
                        AlphaEquivSymmetric(M_sub_N', right_lambda);
                    }

                    ParallelReductionAlphaInvariance(left_lambda, right_lambda, M_sub_N, M_sub_N');
                    assert parallelReduction(M_sub_N, M_sub_N');
                }
                else 
                {

                    var N_and_N' := reunion(vars(N), vars(N'));
                    reunionIsGoodForWork(vars(N), vars(N'));
                    
                    var P_and_N_N' := reunion(vars(P), N_and_N');
                    reunionIsGoodForWork(vars(P), N_and_N');
                    
                    var safe_ids := addition(x, addition(y, P_and_N_N'));
                    var y' := addAnUniqueId(safe_ids)[0];

                    assert !(y' in safe_ids);
                    assert y' != x && y' != y;

                    NotInReunionSoNotInBoth(vars(P), N_and_N', y');
                    NotInReunionSoNotInBoth(vars(N), vars(N'), y');

                    assert !(y' in vars(N)) && !(y' in vars(N'));
                    assert !(y' in vars(P));
                    notInVarsSoNotInFree(N,y');
                    notInVarsSoNotInFree(N',y');
                    notInVarsSoNotInFree(P,y');
                    assert !(y' in free(N)) && !(y' in free(N'));
                    assert !(y' in free(P));

                    var safe_body := substitution(P, y, Var(y'));
                
                    var M_renamed := Lambda(y', safe_body);

                    SubstAlphaEquivalence(P, y, y');
                    assert alphaEquivalence(M, M_renamed);

                    subsitutionOfVarDoesNotChangeHeightFORVARIABLES(P, y, Var(y'));
                    assert lHeight(safe_body) < lHeight(M);
                    
                    parallelReductionSubstitution(safe_body, N, N', x);

                    var sub_P_N := caSubstitution(safe_body, x, N);
                    var sub_P_N' := caSubstitution(safe_body, x, N');
                    
                    var M_renamed_sub_N := caSubstitution(M_renamed, x, N);
                    var M_renamed_sub_N' := caSubstitution(M_renamed, x, N');
                    
                    var left_lambda := Lambda(y', sub_P_N);
                    var right_lambda := Lambda(y', sub_P_N');
                    
                    assert parallelReduction(left_lambda, right_lambda) by {
                        assert parallelReduction(sub_P_N, sub_P_N'); 
                        EqualTermsAreAlphaEquilvalent(Lambda(y', sub_P_N'), right_lambda);
                        assert parallelReduction(sub_P_N, sub_P_N') && alphaEquivalence(Lambda(y', sub_P_N'), right_lambda);
                    }

                    assert M_renamed == Lambda(y', safe_body);
                    SubstPushesIntoSafeLambda(y', safe_body, x, N);
                    assert alphaEquivalence(M_renamed_sub_N, left_lambda); 

                    EqualTermsAreAlphaEquilvalent(N, N);
                    CaSubstEquivalence(M, N, M_renamed, N, x);
                    assert alphaEquivalence(M_sub_N, M_renamed_sub_N);

                    AlphaEquivTransitive(M_sub_N, M_renamed_sub_N, left_lambda);
                    AlphaEquivSymmetric(M_sub_N, left_lambda);

                   assert alphaEquivalence(left_lambda, M_sub_N) ;


                    assert alphaEquivalence(right_lambda, M_sub_N') by {
                        assert M_renamed == Lambda(y', safe_body);
                        SubstPushesIntoSafeLambda(y', safe_body, x, N');
                        assert alphaEquivalence(M_renamed_sub_N', right_lambda); // Utilizing the frozen variable!

                        EqualTermsAreAlphaEquilvalent(N', N');
                        CaSubstEquivalence(M, N', M_renamed, N', x);
                        assert alphaEquivalence(M_sub_N', M_renamed_sub_N');

                        AlphaEquivTransitive(M_sub_N', M_renamed_sub_N', right_lambda);
                        AlphaEquivSymmetric(M_sub_N', right_lambda);
                    }


                    ParallelReductionAlphaInvariance(left_lambda, right_lambda, M_sub_N, M_sub_N');
                    assert parallelReduction(M_sub_N, M_sub_N');
                }
            }
        }
}

lemma parallelReductionSubstitution2(M:LambdaTerm,N:LambdaTerm,M':LambdaTerm,N':LambdaTerm,x:Id)
    requires parallelReduction(N,N') && alphaEquivalence(M,M')
    ensures parallelReduction(caSubstitution(M,x,N),caSubstitution(M',x,N'))
{
    var M_sub_N := caSubstitution(M, x, N);
    var M_sub_N' := caSubstitution(M, x, N');
    var M'_sub_N' := caSubstitution(M', x, N');

    parallelReductionSubstitution(M, N, N', x);

    EqualTermsAreAlphaEquilvalent(N', N');
    CaSubstEquivalence(M, N', M', N', x);

    EqualTermsAreAlphaEquilvalent(M_sub_N, M_sub_N);

    ParallelReductionAlphaInvariance(M_sub_N, M_sub_N', M_sub_N, M'_sub_N');
}
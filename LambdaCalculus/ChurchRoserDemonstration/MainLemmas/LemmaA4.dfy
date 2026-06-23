include "LemmaA3.dfy"

lemma  ParallelReductionMultiSubstitution (M:LambdaTerm,N:LambdaTerm,M':LambdaTerm,N':LambdaTerm,x:Id)
    requires parallelReduction(M,M') && parallelReduction(N,N')
    ensures parallelReduction(caSubstitution(M,x,N),caSubstitution(M',x,N'))
    decreases lHeight(M)
{
    if (alphaEquivalence(M,M'))
    {
        parallelReductionSubstitution2(M,N,M',N',x);
    }
    else 
    { 
        var sub_m:=caSubstitution(M,x,N);
        var sub_m':=caSubstitution(M',x,N');
        match M 
            case Application(P,Q) => 
            {
                var isRule3 := M'.Application? && parallelReduction(P, M'.t1) && parallelReduction(Q, M'.t2);    
                    if (isRule3)
                        {
                            var P_res := M'.t1;
                            var Q_res := M'.t2;
                            SubstDistributesOverApp(P,Q,x,N);
                            SubstDistributesOverApp(P_res,Q_res,x,N');

                            ParallelReductionMultiSubstitution(P,N,P_res,N',x);
                            ParallelReductionMultiSubstitution(Q,N,Q_res,N',x);

                            var sub_p:=caSubstitution(P,x,N);
                            var sub_q:=caSubstitution(Q,x,N);
                            var sub_p':=caSubstitution(P_res,x,N');
                            var sub_q':=caSubstitution(Q_res,x,N');

                            var left_result:=Application(sub_p,sub_q);
                            var right_result:=Application(sub_p',sub_q');

                            assert alphaEquivalence(sub_m,left_result);
                            AlphaEquivSymmetric(sub_m,left_result);
                            assert alphaEquivalence(sub_m',right_result);
                            AlphaEquivSymmetric(sub_m',right_result);

                            assert parallelReduction(sub_p,sub_p');
                            assert parallelReduction(sub_q,sub_q');

                            assert parallelReduction(left_result,right_result);

                            assert alphaEquivalence(left_result,sub_m);
                            assert alphaEquivalence(right_result,sub_m');
                            ParallelReductionAlphaInvariance(left_result,right_result,sub_m,sub_m');
                            assert parallelReduction(sub_m,sub_m');
                             
                        }
                        else 
                        {
                            assert P.Lambda?;
                            var y := P.x;
                            var body := P.t;
                
                            var P', Q' :| parallelReduction(body, P') && parallelReduction(Q, Q') && alphaEquivalence(M', caSubstitution(P', y, Q'));
                    
                            if y != x && !(y in free(N)) && !(y in free(N')) && !(y in free(Q')) {
                        
                                var sub_P_N := caSubstitution(P, x, N);
                                var sub_Q_N := caSubstitution(Q, x, N);
                            
                                var body_sub_N := caSubstitution(body, x, N);
                                var P_prime_sub_N_prime := caSubstitution(P', x, N');
                                var Q_prime_sub_N_prime := caSubstitution(Q', x, N');
                        
                            
                                ParallelReductionMultiSubstitution(body, N, P', N', x) by
                                {
                                    assert parallelReduction(body, P');
                                    assert parallelReduction(N,N');
                                    assert lHeight(body)<lHeight(P)<lHeight(M);
                                }
                                ParallelReductionMultiSubstitution(Q, N, Q', N', x);
                        
                                var left_lambda := Lambda(y, body_sub_N);
                                var left_app := Application(left_lambda, sub_Q_N);
                            
                                SubstDistributesOverApp(P, Q, x, N);
                                SubstPushesIntoSafeLambda(y, body, x, N);
                                EqualTermsAreAlphaEquilvalent(sub_Q_N, sub_Q_N);
                                ApplicationEquivalence(sub_P_N, left_lambda, sub_Q_N, sub_Q_N);
                                AlphaEquivSymmetric(Application(sub_P_N, sub_Q_N),Application(left_lambda, sub_Q_N) );
                                AlphaEquivSymmetric(sub_m, Application(sub_P_N, sub_Q_N));
                                AlphaEquivTransitive(left_app, Application(sub_P_N, sub_Q_N), sub_m);

                                 assert alphaEquivalence(left_app, sub_m) ;
                        
                                var rule4_target := caSubstitution(P_prime_sub_N_prime, y, Q_prime_sub_N_prime);
                            
                                assert parallelReduction(left_app, rule4_target) by {
                                    EqualTermsAreAlphaEquilvalent(rule4_target, rule4_target);
                                    assert parallelReduction(body_sub_N, P_prime_sub_N_prime) && parallelReduction(sub_Q_N, Q_prime_sub_N_prime) && alphaEquivalence(rule4_target, rule4_target);
                                }
                            
                                assert alphaEquivalence(rule4_target, sub_m') by {
                                    var sub_M_raw := caSubstitution(P', y, Q');
                                    AlphaEquivSymmetric(M', sub_M_raw); 
                                    
                                    EqualTermsAreAlphaEquilvalent(N', N');
                                    CaSubstEquivalence(sub_M_raw, N', M', N', x); 
                                
                                SubstitutionLemma(P', Q', N', y, x);
                                
                                AlphaEquivSymmetric(caSubstitution(sub_M_raw, x, N'), rule4_target);
                                AlphaEquivTransitive(rule4_target, caSubstitution(sub_M_raw, x, N'), sub_m');
                                }
                        
                                ParallelReductionAlphaInvariance(left_app, rule4_target, sub_m, sub_m');
                                assert parallelReduction(caSubstitution(M,x,N),caSubstitution(M',x,N'));
                } else {
                        var pool1 := reunion(vars(N), vars(N'));
                        reunionIsGoodForWork(vars(N), vars(N'));
                        var pool2 := reunion(vars(P'), reunion(vars(P), vars(Q')));
                        reunionIsGoodForWork(vars(P), vars(Q'));
                        reunionIsGoodForWork(vars(P'), reunion(vars(P), vars(Q')));
                        var pool3 := reunion(pool1, pool2);
                        reunionIsGoodForWork(pool1, pool2);
                        
                        var safe_ids := addition(x, addition(y, pool3));
                        var y' := addAnUniqueId(safe_ids)[0];

                        NotInReunionSoNotInBoth(pool1, pool2, y');
                        NotInReunionSoNotInBoth(vars(N), vars(N'), y');
                        NotInReunionSoNotInBoth(vars(P'), reunion(vars(P), vars(Q')), y');
                        NotInReunionSoNotInBoth(vars(P), vars(Q'), y');
                        varsOfALambdaIncludesVarsofASubLambda(P);

                        notInVarsSoNotInFree(N, y');
                        notInVarsSoNotInFree(N', y');
                        notInVarsSoNotInFree(Q', y');

                        var safe_body := substitution(body, y, Var(y'));
                        var P_renamed := Lambda(y', safe_body);
                        var M_renamed := Application(P_renamed, Q);

                        SubstAlphaEquivalence(body, y, y');
                        EqualTermsAreAlphaEquilvalent(Q, Q);
                        ApplicationEquivalence(P, P_renamed, Q, Q);

                        subsitutionOfVarDoesNotChangeHeightFORVARIABLES(body, y, Var(y'));
                        
                        var sub_P_renamed_N := caSubstitution(P_renamed, x, N);
                        var sub_Q_N := caSubstitution(Q, x, N);
                        var left_app := Application(sub_P_renamed_N, sub_Q_N);

                        var safe_body_sub_N := caSubstitution(safe_body, x, N);
                        var P_prime_sub_N_prime := caSubstitution(P', x, N'); 
                        var Q_prime_sub_N_prime := caSubstitution(Q', x, N');

                        varsOfALambdaIncludesVarsofASubLambda(P);
                        var P_ren := substitution(P', y, Var(y'));
                        ParRedRename(body, P', y, y');
                        CaSubstIsNaiveWhenFresh(body, y, y');
                        CaSubstIsNaiveWhenFresh(P', y, y');
                        assert parallelReduction(safe_body, P_ren);

                        assert lHeight(M) > lHeight(body);
                        ParallelReductionMultiSubstitution(safe_body, N, P_ren, N', x);
                        ParallelReductionMultiSubstitution(Q, N, Q', N', x);

                        var P2 := caSubstitution(P_ren, x, N');
                        var N2 := caSubstitution(Q', x, N');
                        assert parallelReduction(safe_body_sub_N, P2);
                        assert parallelReduction(sub_Q_N, N2);

                        var LHSapp := Application(Lambda(y', safe_body_sub_N), sub_Q_N);

                        EqualTermsAreAlphaEquilvalent(N, N);
                        CaSubstEquivalence(M, N, M_renamed, N, x);
                        SubstDistributesOverApp(P_renamed, Q, x, N);
                        SubstPushesIntoSafeLambda(y', safe_body, x, N);
                        EqualTermsAreAlphaEquilvalent(sub_Q_N, sub_Q_N);
                        ApplicationEquivalence(caSubstitution(P_renamed, x, N), Lambda(y', safe_body_sub_N), sub_Q_N, sub_Q_N);
                        AlphaEquivTransitive(sub_m, caSubstitution(M_renamed, x, N),
                                             Application(caSubstitution(P_renamed, x, N), sub_Q_N));
                        AlphaEquivTransitive(sub_m,
                                             Application(caSubstitution(P_renamed, x, N), sub_Q_N),
                                             LHSapp);

                        SubstAlphaEquivalence(P', y, y');
                        SubstRespectsBinderAlpha(y, P', y', P_ren, Q');
                        AlphaEquivTransitive(M', caSubstitution(P', y, Q'), caSubstitution(P_ren, y', Q'));
                        EqualTermsAreAlphaEquilvalent(N', N');
                        CaSubstEquivalence(M', N', caSubstitution(P_ren, y', Q'), N', x);
                        SubstitutionLemma(P_ren, Q', N', y', x);
                        AlphaEquivTransitive(sub_m',
                                             caSubstitution(caSubstitution(P_ren, y', Q'), x, N'),
                                             caSubstitution(P2, y', N2));

                        ParRedBetaIntro(y', safe_body_sub_N, sub_Q_N, P2, N2, sub_m');
                        AlphaEquivSymmetric(sub_m, LHSapp);
                        EqualTermsAreAlphaEquilvalent(sub_m', sub_m');
                        ParallelReductionAlphaInvariance(LHSapp, sub_m', sub_m, sub_m');
                }
                        }
                    
            } 
            case Lambda(y,body)=>
            {
                var r :| parallelReduction(body, r) && alphaEquivalence(Lambda(y, r), M');
                var S := addition(x, reunion(vars(M), reunion(vars(M'), reunion(vars(r), reunion(vars(N), vars(N'))))));
                reunionIncludesBothSets(vars(N), vars(N'));
                reunionIncludesBothSets(vars(r), reunion(vars(N), vars(N')));
                reunionIncludesBothSets(vars(M'), reunion(vars(r), reunion(vars(N), vars(N'))));
                reunionIncludesBothSets(vars(M), reunion(vars(M'), reunion(vars(r), reunion(vars(N), vars(N')))));
                var y' := addAnUniqueId(S)[0];
                assert !(y' in S);
                assert y' != x;
                varsOfALambdaIncludesVarsofASubLambda(M);
                assert !(y' in vars(M)) && !(y' in vars(M')) && !(y' in vars(r)) && !(y' in vars(N)) && !(y' in vars(N'));
                assert !(y' in vars(body));
                notInVarsSoNotInFree(N, y');
                notInVarsSoNotInFree(N', y');

                var body_alt := substitution(body, y, Var(y'));
                var r_alt := substitution(r, y, Var(y'));
                ParRedRename(body, r, y, y');
                CaSubstIsNaiveWhenFresh(body, y, y');
                CaSubstIsNaiveWhenFresh(r, y, y');
                assert parallelReduction(body_alt, r_alt);
                subsitutionOfVarDoesNotChangeHeightFORVARIABLES(body, y, Var(y'));
                ParallelReductionMultiSubstitution(body_alt, N, r_alt, N', x);
                var PbA := caSubstitution(body_alt, x, N);
                var rr := caSubstitution(r_alt, x, N');
                assert parallelReduction(PbA, rr);


                SubstAlphaEquivalence(body, y, y');
                EqualTermsAreAlphaEquilvalent(N, N);
                CaSubstEquivalence(M, N, Lambda(y', body_alt), N, x);
                SubstPushesIntoSafeLambda(y', body_alt, x, N);
                AlphaEquivTransitive(sub_m, caSubstitution(Lambda(y', body_alt), x, N), Lambda(y', PbA));

                SubstAlphaEquivalence(r, y, y');
                AlphaEquivSymmetric(Lambda(y, r), Lambda(y', r_alt));
                AlphaEquivTransitive(Lambda(y', r_alt), Lambda(y, r), M');
                EqualTermsAreAlphaEquilvalent(N', N');
                CaSubstEquivalence(Lambda(y', r_alt), N', M', N', x);
                SubstPushesIntoSafeLambda(y', r_alt, x, N');
                AlphaEquivSymmetric(caSubstitution(Lambda(y', r_alt), x, N'), Lambda(y', rr));
                AlphaEquivTransitive(Lambda(y', rr), caSubstitution(Lambda(y', r_alt), x, N'), sub_m');

                ParRedLambdaIntro(y', PbA, rr, sub_m');
                AlphaEquivSymmetric(sub_m, Lambda(y', PbA));
                EqualTermsAreAlphaEquilvalent(sub_m', sub_m');
                ParallelReductionAlphaInvariance(Lambda(y', PbA), sub_m', sub_m, sub_m');
            }
    }
}
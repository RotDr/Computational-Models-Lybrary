include "BetaReduction.dfy"
include "LemmaA5AndA6.dfy"
include "LemmaA4.dfy"
include "LemmaA3.dfy"

lemma {:vcs_split_on_every_assert}DiamondLemma (M:LambdaTerm,M1:LambdaTerm,M2:LambdaTerm)
    requires parallelReduction(M,M1)
    requires parallelReduction(M,M2)
    ensures exists M3:LambdaTerm::parallelReduction(M1,M3) && parallelReduction(M2,M3)
    decreases lHeight(M)
{

    assert (alphaEquivalence(M,M1) || rule2(M,M1) || rule3(M,M1) || rule4(M,M1)) <==> parallelReduction(M,M1);
    if (alphaEquivalence(M,M1))
    {
        EqualTermsAreAlphaEquilvalent(M2,M2);
        ParallelReductionAlphaInvariance(M,M2,M1,M2);
        var M3:=M2;
        assert parallelReduction(M1,M3) && parallelReduction(M2,M3);
    }
    else 
    {
        if (rule3(M,M1))
        {
            match M 
                case Application(P,Q) =>
                {
                    match M1
                        case Application(P',Q') =>
                        {
                            assert parallelReduction(P,P');
                            assert parallelReduction(Q,Q');

                            assert parallelReduction(Application(P,Q),M2);

                            AlphaParallelLemma(P,Q,M2);
                            var part1:=(exists P'2: LambdaTerm, Q'2: LambdaTerm :: 
                            parallelReduction(P, P'2) && parallelReduction(Q, Q'2) && alphaEquivalence(Application(P'2, Q'2), M2));
                            if (part1)
                            {
                                var P'2:LambdaTerm,Q'2:LambdaTerm :|parallelReduction(P, P'2) && 
                                parallelReduction(Q, Q'2) && alphaEquivalence(Application(P'2, Q'2), M2);

                                assert parallelReduction(P,P');
                                assert parallelReduction(P,P'2);
                                DiamondLemma(P,P',P'2);
                                var P'3:| parallelReduction(P',P'3) && parallelReduction(P'2,P'3);

                                assert parallelReduction(Q,Q');
                                assert parallelReduction(Q,Q'2);
                                DiamondLemma(Q,Q',Q'2);
                                var Q'3:| parallelReduction(Q',Q'3) && parallelReduction(Q'2,Q'3);

                                var right_result:=Application(P'2,Q'2);
                                var M3:=Application(P'3,Q'3);

                                assert parallelReduction(Q'2,Q'3) && parallelReduction(P'2,P'3);
                                assert rule3(right_result,M3);
                                EqualTermsAreAlphaEquilvalent(M3,M3);
                                ParallelReductionAlphaInvariance(right_result,M3,M2,M3);

                                assert parallelReduction(M2,M3); 

                                assert parallelReduction(Q',Q'3) && parallelReduction(P',P'3);

                                assert rule3(M1,M3);

                                assert parallelReduction(M1,M3) && parallelReduction(M2,M3);
                            }
                            else 
                            {
                                assert (P.Lambda? && 
                                        exists P1'': LambdaTerm, Q'': LambdaTerm :: 
                                            parallelReduction(P.t, P1'') 
                                            && parallelReduction(Q, Q'') 
                                            && alphaEquivalence(M2, caSubstitution(P1'', P.x, Q'')));

                                var P1:LambdaTerm,x:Id:|P==Lambda(x,P1);

                                var P1'2:LambdaTerm,Q'2:LambdaTerm :| parallelReduction(P.t, P1'2) 
                                            && parallelReduction(Q, Q'2) 
                                            && alphaEquivalence(M2, caSubstitution(P1'2, P.x, Q'2));


                                assert parallelReduction(P,P'); 
                                LambdaParallelLemma(P1,P',x);
                                
                                var P1':LambdaTerm:| parallelReduction(P1,P1') && alphaEquivalence(Lambda(x,P1'),P');
                                var P'_result:=Lambda(x,P1');

                                assert parallelReduction(P1,P1') && parallelReduction(P1,P1'2);
                                assert parallelReduction(Q,Q') && parallelReduction(Q,Q'2);

                                assert lHeight(P1)<lHeight(Lambda(x,P1))==lHeight(P)<lHeight(M);
                                DiamondLemma(P1,P1',P1'2);
                                DiamondLemma(Q,Q',Q'2);

                                var P1'3:LambdaTerm:|parallelReduction(P1',P1'3) && parallelReduction(P1'2,P1'3);
                                var Q'3:LambdaTerm:|parallelReduction(Q',Q'3) && parallelReduction(Q'2,Q'3);

                                EqualTermsAreAlphaEquilvalent(Q',Q');
                                AlphaEquivSymmetric(P'_result,P');
                                ApplicationEquivalence(P',P'_result,Q',Q');
                                var M1_result:=Application(P'_result,Q');
                                assert alphaEquivalence(M1,M1_result);

                                var M3 := caSubstitution(P1'3, x, Q'3);
                                assert alphaEquivalence(M2, caSubstitution(P1'2, x, Q'2));


                                EqualTermsAreAlphaEquilvalent(M3,M3);
                                assert rule4(M1_result, M3) by {
                                    assert parallelReduction(P1', P1'3);
                                    assert parallelReduction(Q', Q'3);
                                    assert alphaEquivalence(M3, caSubstitution(P1'3, x, Q'3));
                                }

                                assert parallelReduction(M1_result,M3);

                                AlphaEquivSymmetric(M1, M1_result);
                                ParallelReductionAlphaInvariance(M1_result, M3, M1, M3);

                                ParallelReductionMultiSubstitution(P1'2, Q'2, P1'3, Q'3, x);
                                AlphaEquivSymmetric(M2, caSubstitution(P1'2, x, Q'2));
                                ParallelReductionAlphaInvariance(caSubstitution(P1'2, x, Q'2), M3, M2, M3);

                                assert parallelReduction(M1, M3) && parallelReduction(M2, M3);
                            }
                        }
                }
                case _ => 
                {
                    assert false;
                }
        }
        else 
        {
            if (rule4(M,M1))
            {
                assert M.Application?;
                assert M.t1.Lambda?;

                var x:Id,P:LambdaTerm,Q:LambdaTerm :| M==Application(Lambda(x,P),Q);

                var P':LambdaTerm,Q':LambdaTerm:| parallelReduction(P,P') && parallelReduction(Q,Q') && alphaEquivalence(M1,caSubstitution(P',x,Q'));

                AlphaParallelLemma(Lambda(x,P),Q,M2);

                var part1:=        (exists P'2_temp: LambdaTerm, Q'2: LambdaTerm :: 
                parallelReduction(Lambda(x,P),P'2_temp) && parallelReduction(Q, Q'2) && alphaEquivalence(Application(P'2_temp, Q'2), M2));

                if (part1)
                {
                    var P'2_temp: LambdaTerm, Q'2: LambdaTerm :|
                        parallelReduction(Lambda(x,P),P'2_temp) && parallelReduction(Q, Q'2) && alphaEquivalence(Application(P'2_temp, Q'2), M2);

                    LambdaParallelLemma(P,P'2_temp,x);
                    var P'2: LambdaTerm :| parallelReduction(P, P'2) && alphaEquivalence(Lambda(x, P'2), P'2_temp);

                    assert parallelReduction(P,P'2) && parallelReduction(P,P');
                    assert parallelReduction(Q,Q'2) && parallelReduction(Q,Q');

                    assert lHeight(P)<lHeight(Lambda(x,P))<lHeight(M);
                    DiamondLemma(P,P',P'2);
                    DiamondLemma(Q,Q',Q'2);

                    var P'3:|parallelReduction(P',P'3) && parallelReduction(P'2,P'3);
                    var Q'3:|parallelReduction(Q',Q'3) && parallelReduction(Q'2,Q'3); 

                    var M1_new:=caSubstitution(P',x,Q');
                    var M3:=caSubstitution(P'3,x,Q'3);
                    ParallelReductionMultiSubstitution(P',Q',P'3,Q'3,x);
                    ParallelReductionMultiSubstitution(P'2,Q'2,P'3,Q'3,x);

                    assert parallelReduction(M1_new,M3);
                    EqualTermsAreAlphaEquilvalent(M3,M3);

                    AlphaEquivSymmetric(M1,M1_new);
                    ParallelReductionAlphaInvariance(M1_new,M3,M1,M3);

                    assert parallelReduction(M1,M3);

                    assert rule4(Application(Lambda(x,P'2),Q'2),M3)==true;

                    EqualTermsAreAlphaEquilvalent(Q'2,Q'2);

                    assert alphaEquivalence(Lambda(x, P'2), P'2_temp); 
                    assert alphaEquivalence(Q'2,Q'2);

                    ApplicationEquivalence(Lambda(x,P'2),P'2_temp,Q'2,Q'2) by {
                        assert alphaEquivalence(Lambda(x, P'2), P'2_temp); 
                        assert alphaEquivalence(Q'2,Q'2);
                }

                    
                    var M2_result_2:=Application(Lambda(x, P'2),Q'2);

                    var M2_result_1:=Application(P'2_temp,Q'2);

                    assert alphaEquivalence(M2_result_2,M2_result_1);

                    assert alphaEquivalence(Application(P'2_temp, Q'2), M2);
                    assert alphaEquivalence(M2_result_1,M2);

                    AlphaEquivTransitive(M2_result_2,M2_result_1,M2);

                    ParallelReductionAlphaInvariance(M2_result_2,M3,M2,M3);

                    assert parallelReduction(M2,M3) ;
                    assert parallelReduction(M1,M3);

                }
                else 
                {
                    assert  (Lambda(x,P).Lambda? && 
                        exists P'2: LambdaTerm, Q'2: LambdaTerm :: 
                             parallelReduction(P, P'2) && parallelReduction(Q, Q'2) && alphaEquivalence(M2, caSubstitution(P'2, x, Q'2)));

                    assert exists P'2: LambdaTerm, Q'2: LambdaTerm :: 
                             parallelReduction(P, P'2) && parallelReduction(Q, Q'2) && alphaEquivalence(M2, caSubstitution(P'2, x, Q'2));

                    var P'2: LambdaTerm, Q'2: LambdaTerm :| 
                             parallelReduction(P, P'2) && parallelReduction(Q, Q'2) && alphaEquivalence(M2, caSubstitution(P'2, x, Q'2));

                    assert parallelReduction(P,P') && parallelReduction(P,P'2);
                    assert parallelReduction(Q,Q') && parallelReduction(Q,Q'2);

                    assert lHeight(P)<lHeight(Lambda(x,P))<lHeight(M);
                    DiamondLemma(P,P',P'2);
                    DiamondLemma(Q,Q',Q'2);

                    var P'3:LambdaTerm:|parallelReduction(P',P'3) && parallelReduction(P'2,P'3);
                    var Q'3:LambdaTerm:|parallelReduction(Q',Q'3) && parallelReduction(Q'2,Q'3);

                    var M1_new:=caSubstitution(P',x,Q');

                    assert alphaEquivalence(M1,M1_new);
                    AlphaEquivSymmetric(M1,M1_new);

                    assert parallelReduction(P',P'3);
                    assert parallelReduction(Q',Q'3);

                    ParallelReductionMultiSubstitution(P',Q',P'3,Q'3,x) ;

                    var M3:=caSubstitution(P'3,x,Q'3);

                    assert parallelReduction(M1_new,M3);

                    EqualTermsAreAlphaEquilvalent(M3,M3);

                    ParallelReductionAlphaInvariance(M1_new,M3,M1,M3);

                    assert parallelReduction(M1,M3);    

                    assert parallelReduction(P'2,P'3);
                    assert parallelReduction(Q'2,Q'3);

                    ParallelReductionMultiSubstitution(P'2,Q'2,P'3,Q'3,x) ;

                    var M2_new:=caSubstitution(P'2,x,Q'2);
                    assert  alphaEquivalence(M2, M2_new);
                    AlphaEquivSymmetric(M2,M2_new);

                    assert parallelReduction(M2_new,M3);
                    ParallelReductionAlphaInvariance(M2_new,M3,M2,M3);

                    assert parallelReduction(M2,M3);
                }

            }  
            else 
            {
                assert rule2(M,M1);
                match M 
                    case Lambda(x,P) =>
                    {
                        assert    exists P': LambdaTerm ::
                                parallelReduction(P, P') && alphaEquivalence(Lambda(x, P'), M1);
                        var P': LambdaTerm :|
                                parallelReduction(P, P') && alphaEquivalence(Lambda(x, P'), M1);
                        
                        var M1_new:=Lambda(x,P');

                        LambdaParallelLemma(P,M2,x);
                        assert exists P'2: LambdaTerm :: parallelReduction(P, P'2) && alphaEquivalence(Lambda(x, P'2), M2) ;
                            
                        var P'2:LambdaTerm:| parallelReduction(P, P'2) && alphaEquivalence(Lambda(x, P'2), M2);

                        var M2_new:=Lambda(x, P'2);
                        assert alphaEquivalence(M2_new,M2);

                        assert parallelReduction(P,P');
                        assert parallelReduction(P,P'2);

                        assert lHeight(P)<lHeight(M);
                        DiamondLemma(P,P',P'2);

                        var P'3:|parallelReduction(P',P'3) && parallelReduction(P'2,P'3);

                        var M3:=Lambda(x,P'3);
                        
                        EqualTermsAreAlphaEquilvalent(M3,M3);
                        assert rule2(M1_new,M3);
                        assert rule2(M2_new,M3);

                        assert parallelReduction(M1_new,M3);
                        assert parallelReduction(M2_new,M3);
                        ParallelReductionAlphaInvariance(M1_new,M3,M1,M3);
                        ParallelReductionAlphaInvariance(M2_new,M3,M2,M3);
                        assert parallelReduction(M1,M3) && parallelReduction(M2,M3);

                    }
            }
        }
    }
}


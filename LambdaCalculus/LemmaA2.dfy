include "HelperLemmasForA2.dfy"

lemma SubstitutionLemma (M:LambdaTerm,N:LambdaTerm,P:LambdaTerm,x:Id,y:Id)
    requires x!=y
    requires !(x in free(P))
    ensures alphaEquivalence(caSubstitution(caSubstitution(M,x,N),y,P),caSubstitution(caSubstitution(M,y,P),x,caSubstitution(N,y,P)))
    decreases lHeight(M)

{
    match M
        case Application(M1,M2) =>
        {
            SubstitutionLemma(M1, N, P, x, y);
            SubstitutionLemma(M2, N, P, x, y);

            var N_sub_y := caSubstitution(N, y, P);

            var M1_left := caSubstitution(caSubstitution(M1, x, N), y, P);
            var M1_right := caSubstitution(caSubstitution(M1, y, P), x, N_sub_y);
            var M2_left := caSubstitution(caSubstitution(M2, x, N), y, P);
            var M2_right := caSubstitution(caSubstitution(M2, y, P), x, N_sub_y);

            var app_left := Application(M1_left, M2_left);
            var app_right := Application(M1_right, M2_right);
            
            ApplicationEquivalence(M1_left, M1_right, M2_left, M2_right);

            var M_left_actual := caSubstitution(caSubstitution(M, x, N), y, P);
            var M_right_actual := caSubstitution(caSubstitution(M, y, P), x, N_sub_y);

            var inner_left := caSubstitution(M, x, N);
            var inner_left_dist := Application(caSubstitution(M1, x, N), caSubstitution(M2, x, N));
            
            SubstDistributesOverApp(M1, M2, x, N);
             EqualTermsAreAlphaEquilvalent(P, P);
             assert alphaEquivalence(inner_left,inner_left_dist);
             assert alphaEquivalence(P,P);
             CaSubstEquivalence(inner_left,P, inner_left_dist, P, y);
            
            var mid_left := caSubstitution(inner_left_dist, y, P);
            SubstDistributesOverApp(caSubstitution(M1, x, N), caSubstitution(M2, x, N), y, P);
           AlphaEquivTransitive(M_left_actual, mid_left, app_left);

            var inner_right := caSubstitution(M, y, P);
            var inner_right_dist := Application(caSubstitution(M1, y, P), caSubstitution(M2, y, P));
            
            SubstDistributesOverApp(M1, M2, y, P);
            EqualTermsAreAlphaEquilvalent(N_sub_y, N_sub_y);
            CaSubstEquivalence(inner_right,N_sub_y ,inner_right_dist, N_sub_y, x);
            
            var mid_right := caSubstitution(inner_right_dist, x, N_sub_y);
            SubstDistributesOverApp(caSubstitution(M1, y, P), caSubstitution(M2, y, P), x, N_sub_y);
            AlphaEquivTransitive(M_right_actual, mid_right, app_right);

            AlphaEquivSymmetric(M_right_actual, app_right);
            AlphaEquivTransitive(M_left_actual, app_left, app_right);
            AlphaEquivTransitive(M_left_actual, app_right, M_right_actual);

            assert alphaEquivalence(caSubstitution(caSubstitution(M,x,N),y,P),caSubstitution(caSubstitution(M,y,P),x,caSubstitution(N,y,P)));
        }
        case Lambda(z,M')=>
        {
                var P_and_M := reunion(freeVec(P), vars(M'));
                var N_P_M := reunion(freeVec(N), P_and_M);
                var safe_ids := addition(x, addition(y, N_P_M));

                var new_id := addAnUniqueId(safe_ids)[0];

                assert !(new_id in safe_ids);
                assert new_id != x && new_id != y;

                NotInReunionSoNotInBoth(freeVec(N), P_and_M, new_id);
                assert !(new_id in freeVec(N));
                assert !(new_id in free(N));

                NotInReunionSoNotInBoth(freeVec(P), vars(M'), new_id);
                assert !(new_id in freeVec(P));
                assert !(new_id in free(P));
                assert !(new_id in vars(M'));

                var new_M := Lambda(new_id, substitution(M', z, Var(new_id)));

                SubstAlphaEquivalence(M', z, new_id);

                var safe_body := substitution(M', z, Var(new_id));
                assert alphaEquivalence(Lambda(z, M'), Lambda(new_id, safe_body));

                assert alphaEquivalence(M, new_M);

                subsitutionOfVarDoesNotChangeHeightFORVARIABLES(M', z, Var(new_id));
                assert lHeight(safe_body) == lHeight(M') < lHeight(M);
                SubstitutionLemma(safe_body, N, P, x, y);

                var M'_left  := caSubstitution(caSubstitution(safe_body, x, N), y, P);
                var M'_right := caSubstitution(caSubstitution(safe_body, y, P), x, caSubstitution(N, y, P));
                assert alphaEquivalence(M'_left, M'_right);

                AlphaCongruenceLambda(new_id, M'_left, M'_right);
                var left_result  := Lambda(new_id, M'_left);
                var right_result := Lambda(new_id, M'_right);   
                assert alphaEquivalence(left_result, right_result);



                var inner_left_sub := caSubstitution(new_M, x, N);
                assert x != new_id;

                SubstPushesIntoSafeLambda(new_id, safe_body, x, N);
                var pushed_inner_left := Lambda(new_id, caSubstitution(safe_body, x, N));


                EqualTermsAreAlphaEquilvalent(P, P);
                CaSubstEquivalence(inner_left_sub, P, pushed_inner_left, P, y);
                var outer_left_sub := caSubstitution(inner_left_sub, y, P);


                SubstPushesIntoSafeLambda(new_id, caSubstitution(safe_body, x, N), y, P);

                AlphaEquivTransitive(outer_left_sub,
                                    caSubstitution(pushed_inner_left, y, P),
                                    left_result);

                var N_sub_y := caSubstitution(N, y, P);
                var actual_left := caSubstitution(caSubstitution(M, x, N), y, P);

                EqualTermsAreAlphaEquilvalent(N, N);
                CaSubstEquivalence(M, N, new_M, N, x);
                CaSubstEquivalence(caSubstitution(M, x, N), P,
                                caSubstitution(new_M, x, N), P, y);

                AlphaEquivTransitive(actual_left, outer_left_sub, left_result);


                var inner_right_sub := caSubstitution(new_M, y, P);
                SubstPushesIntoSafeLambda(new_id, safe_body, y, P);
                var pushed_inner_right := Lambda(new_id, caSubstitution(safe_body, y, P));


                EqualTermsAreAlphaEquilvalent(N_sub_y, N_sub_y);
                CaSubstEquivalence(inner_right_sub, N_sub_y,
                                pushed_inner_right, N_sub_y, x);
                var outer_right_sub := caSubstitution(inner_right_sub, x, N_sub_y);


                TheFreeOfCaSub(N, y, P, new_id);

                SubstPushesIntoSafeLambda(new_id, caSubstitution(safe_body, y, P), x, N_sub_y);

                AlphaEquivTransitive(outer_right_sub,
                                    caSubstitution(pushed_inner_right, x, N_sub_y),
                                    right_result);


                var actual_right := caSubstitution(caSubstitution(M, y, P), x, N_sub_y);

                EqualTermsAreAlphaEquilvalent(P, P);
                CaSubstEquivalence(M, P, new_M, P, y);
                CaSubstEquivalence(caSubstitution(M, y, P), N_sub_y,
                                caSubstitution(new_M, y, P), N_sub_y, x);


                AlphaEquivTransitive(actual_left, left_result, right_result);
                AlphaEquivSymmetric(outer_right_sub, right_result);
                AlphaEquivTransitive(actual_left, right_result, outer_right_sub);
                AlphaEquivSymmetric(actual_right, outer_right_sub);
                AlphaEquivTransitive(actual_left, outer_right_sub, actual_right);

            assert alphaEquivalence(
                caSubstitution(caSubstitution(M, x, N), y, P),
                caSubstitution(caSubstitution(M, y, P), x, caSubstitution(N, y, P))
            );
        }
        case Var(z) => {
            if (z == x) {
                var partial_result_left := caSubstitution(M, x, N);
                assert partial_result_left == N;
                
                var left_result := caSubstitution(N, y, P);

                var partial_result_right := caSubstitution(M, y, P);
                assert partial_result_right == M;
                
                var N_sub := caSubstitution(N, y, P);
                var right_result := caSubstitution(partial_result_right, x, N_sub);
                assert right_result == N_sub; 

                assert left_result == right_result;
                EqualTermsAreAlphaEquilvalent(left_result, right_result);
            }
            else if (z == y) {
                var partial_result_left := caSubstitution(M, x, N);
                assert partial_result_left == M; // Because x != y
                
                var left_result := caSubstitution(M, y, P);
                assert left_result == P; 

                var partial_result_right := caSubstitution(M, y, P);
                assert partial_result_right == P; 
                
                var N_sub := caSubstitution(N, y, P);
                
                var right_result := caSubstitution(P, x, N_sub); 

                NoFreeVariablesToReplace(P, x, N_sub);

                AlphaEquivSymmetric(right_result, P);
                assert alphaEquivalence(left_result, right_result);

            }
            else {
                var partial_result_left := caSubstitution(M, x, N);
                assert partial_result_left == M;
                
                var left_result := caSubstitution(partial_result_left, y, P);
                assert left_result == M;

                var partial_result_right := caSubstitution(M, y, P);
                assert partial_result_right == M;
                
                var N_sub := caSubstitution(N, y, P);
                var right_result := caSubstitution(partial_result_right, x, N_sub);
                assert right_result == M;

                assert left_result == right_result;
                EqualTermsAreAlphaEquilvalent(left_result, right_result);
            }
        } 
    
    

}
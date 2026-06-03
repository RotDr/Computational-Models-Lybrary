include "Lambda.dfy"
include "BetaReduction.dfy"


ghost predicate parallelReduction(t1:LambdaTerm,t2:LambdaTerm)
    decreases lHeight(t1)
{
    t1==t2 ||
    match t1 
            case Application(t1a,t1b) =>( match t2 
                                        case Application(t2a,t2b) => parallelReduction(t1a,t2a) && parallelReduction(t1b,t2b)
                                        case _ => false
            ) ||
            ( match t1a 
                    case Lambda(x,M) => ( 
                     exists M': LambdaTerm, N': LambdaTerm ::
              assert lHeight(M)<lHeight(t1);       
              parallelReduction(M, M')          
              && parallelReduction(t1b, N')    
              && t2 == substitution(M', x, N') 
                    )
                    case _=> false
            ) 
            case Lambda(x,t1a) => (
                ( match t2 
                                        case Lambda(y,t2a)=> x==y && parallelReduction(t1a,t2a)
                                        case _ => false
            )
            )
            case _ => false
}

lemma parallelReductionIsReflexive (t:LambdaTerm)
    ensures parallelReduction(t,t)
{

}

// lemma NoFreeVariablesToReplace (M:LambdaTerm,x:Id,P:LambdaTerm)
//     requires !(x in free(M))
//     ensures alphaEquivalence(caSubstitution(M,x,P),M) 
// {
//     var ids:=reunion(vars(M),vars(P));
//     reunionIncludesBothSets(vars(M),vars(P));
//     NoFreeVariablesToReplace'(M,x,P,ids);
// }
lemma NotInReunionSoNotInBoth(s1:seq<Id>,s2:seq<Id>,x:Id)
    requires allUnique(s1) && allUnique(s2)
    requires !(x in reunion(s1,s2))
    ensures !(x in s1) && !(x in s2)
{

}
lemma NotInFreeAndNotFoundInLambdaSoNotInFree(t:LambdaTerm,x:Id,y:Id)
    requires x!=y
    requires !(x in free(Lambda(y,t)))
    ensures !(x in free(t))
{

}

lemma SubstitutionPreservesNonFree(t: LambdaTerm, y: Id, vari: LambdaTerm, x: Id)
    requires x != y
    requires match vari case Var(z) => x != z case _ => false
    requires !(x in free(t))
    ensures !(x in free(substitution(t, y, vari)))
    decreases lHeight(t)
{
    match t {
        case Var(z) => {
        }
        case Lambda(z, t') => {
            if z == y {
            } else {
                if x != z {
                    assert !(x in free(t'));
                    SubstitutionPreservesNonFree(t', y, vari, x);
                }
            }
        }
        case Application(t1, t2) => {
            assert !(x in free(t1)) && !(x in free(t2));
            SubstitutionPreservesNonFree(t1, y, vari, x);
            SubstitutionPreservesNonFree(t2, y, vari, x);
        }
    }
}
lemma NoFreeVariablesToReplace' (M:LambdaTerm,x:Id,P:LambdaTerm,M_sub:LambdaTerm,ids:seq<Id>)
    requires !(x in free(M))
    requires allUnique(ids)
    requires var s1:=vars(M);
         allUnique(s1) && includes(ids,s1)
    requires var s2:=vars(P);
         allUnique(s2)  && includes(ids,s2)
    requires M_sub==caSubstitution'(M,x,P,ids)
    ensures alphaEquivalence(M_sub,M) 
    decreases M
{
    match M 
        case Var(y) =>{
            assert y in free(M);
            assert !(x in free(M));
            assert x!=y;

            assert M_sub==M ;
            EqualTermsAreAlphaEquilvalent(M_sub,M);
        }
        case Application(M1,M2) => 
        {

            ASubLambdaOfAUniqueLambdaIsUnique(M);
            varsOfALambdaIncludesVarsofASubLambda(M);

            var M1' := caSubstitution'(M1, x, P, ids);
            var M2' := caSubstitution'(M2, x, P, ids);

            assert M_sub == Application(M1', M2');

            NoFreeVariablesToReplace'(M1, x, P, M1', ids);
            NoFreeVariablesToReplace'(M2, x, P, M2', ids);


            ApplicationEquivalence(M1', M1, M2', M2);

        }
        case Lambda(y,M') =>
        { 
            if (x==y)
            {
                assert M_sub==M;
                EqualTermsAreAlphaEquilvalent(M_sub,M);
            }
            else 
            {
                if !(y in free(P)) {

                    ASubLambdaOfAUniqueLambdaIsUnique(M);
                    varsOfALambdaIncludesVarsofASubLambda(M);
                    NotInFreeAndNotFoundInLambdaSoNotInFree(M',x,y);

                    var M'_sub:=caSubstitution'(M',x,P,ids);
                    assert M_sub==Lambda(y,M'_sub);
                    NoFreeVariablesToReplace'(M',x,P,M'_sub,ids);

                    AlphaCongruenceLambda(y,M'_sub,M');
                    assert alphaEquivalence(M_sub,M);
                }  
                else 
                {
                    assume alphaEquivalence(M_sub,M);

                        var ids' := addAnUniqueId(ids);
                    var y'   := ids'[0];
                    var vari := Var(y');
                    var M'_renamed := substitution(M', y, vari);
                    var M'_sub     := caSubstitution'(M'_renamed, x, P, ids');

                    assert M_sub == Lambda(y', M'_sub);

                    // Step 1: y' is fresh w.r.t. M'
                    // ids includes vars(M) which includes vars(M'), and y' = ids'[0] ∉ ids
                    assert !(y' in ids);
                    assert includes(ids, vars(M'));  // from varsOfALambdaIncludesVarsofASubLambda + ASubLambdaOfAUniqueLambdaIsUnique
                    assert !(y' in vars(M'));

                    // Step 2: substitution of y->y' in M' doesn't change height
                    subsitutionOfVarDoesNotChangeHeightFORVARIABLES(M', y, vari);


                    ASubLambdaOfAUniqueLambdaIsUnique(M);
                    varsOfALambdaIncludesVarsofASubLambda(M);
                    newIdsDueToSubstitution(M', y, vari, ids');


                    NotInFreeAndNotFoundInLambdaSoNotInFree(M', x, y);
                    assert !(x in free(M'));

                    SubstitutionPreservesNonFree(M', y, vari, x);   
                    assert !(x in free(M'_renamed));


                    NoFreeVariablesToReplace'(M'_renamed, x, P, M'_sub, ids');
                    assert alphaEquivalence(M'_sub, M'_renamed);

                    
                    AlphaCongruenceLambda(y', M'_sub, M'_renamed);
                    assert alphaEquivalence(Lambda(y', M'_sub), Lambda(y', M'_renamed));

                    SubstAlphaEquivalence(M', y, y');
                   
                    AlphaEquivSymmetric(Lambda(y, M'), Lambda(y', M'_renamed));
                    assert alphaEquivalence(Lambda(y', M'_renamed), Lambda(y, M'));

                    AlphaEquivTransitive(Lambda(y', M'_sub), Lambda(y', M'_renamed), Lambda(y, M'));
                    assert alphaEquivalence(M_sub, M);
                }
            }

        }
}

// lemma SubstitutionLemma (M:LambdaTerm,N:LambdaTerm,P:LambdaTerm,x:Id,y:Id)
//     requires x!=y
//     requires !(x in free(P))
//     ensures caSubstitution(caSubstitution(M,x,N),y,P)==caSubstitution(caSubstitution(M,y,P),x,caSubstitution(N,y,P))

// {
//     match M
//         case Application(M1,M2) =>
//         {

//         }
//         case Lambda(z,M')=>
//         {
            
//         }
//         case Var(z) => {
//             if (z==x) 
//             {
//                 var partial_result_left:=caSubstitution(M,x,N);
//                 assert M==Var(x);
//                 assert partial_result_left==N;
//                 var left_result:=caSubstitution(N,y,P);
//                 assert caSubstitution(caSubstitution(M,x,N),y,P)==left_result;

//                 assert x!=y;
//                 var partial_result_right:=caSubstitution(M,y,P);
//                 assert partial_result_right==M;
//                 var result_right:=caSubstitution(partial_result_right,x,caSubstitution(N,y,P));
//                 assert M==Var(x);
//                 assert result_right==caSubstitution(N,y,P);

//                 assert caSubstitution(caSubstitution(M,y,P),x,caSubstitution(N,y,P))==result_right;
                
//                 assert left_result=result_right;
                
//             }
//             if (z==y)
//             {
//                 var partial_result_left:=caSubstitution(M,x,N);
//                 assert M==Var(y);
//                 assert x!=y;
//                 assert partial_result_left==M;
//                 var left_result:=caSubstitution(M,y,P);
//                 assert caSubstitution(M,y,P)==P;
//                 assert caSubstitution(caSubstitution(M,x,N),y,P)==left_result;

//                 var partial_result_right:=caSubstitution(M,y,P);
//                 assert partial_result_right==P; 
//                 var right_result:=caSubstitution(P,caSubstitution(x,caSubstitution(N,y,P)));

//             }
//         } 
    
    

// }
include "Lambda.dfy"
include "BetaReduction.dfy"


ghost predicate parallelReduction(t1:LambdaTerm, t2:LambdaTerm)
    decreases lHeight(t1)
{
    alphaEquivalence(t1, t2) ||
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
ghost predicate rule2(t1:LambdaTerm,t2:LambdaTerm)
    ensures rule2(t1,t2) ==> parallelReduction(t1,t2)
{
    match t1 
        case Lambda(x, body1) =>
            exists r: LambdaTerm ::
                parallelReduction(body1, r) && alphaEquivalence(Lambda(x, r), t2)
        case _=> false
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
lemma LambdaParallelLemma (M:LambdaTerm,N:LambdaTerm,x:Id)
    requires parallelReduction(Lambda(x,M),N)
    ensures exists M': LambdaTerm :: parallelReduction(M, M') && alphaEquivalence(Lambda(x, M'), N)
{
    if alphaEquivalence(Lambda(x, M), N) {
        ParallelReductionIsReflexive(M);
    } 

}


lemma AlphaParallelLemma(M: LambdaTerm, N: LambdaTerm, L: LambdaTerm)
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
        var isRule3 := match L 
            case Application(t2a, t2b) => parallelReduction(M, t2a) && parallelReduction(N, t2b)
            case _ => false;

        if isRule3 {
            var M' := L.t1;
            var N' := L.t2;
            EqualTermsAreAlphaEquilvalent(Application(M', N'), L);
            assert parallelReduction(M, M') && parallelReduction(N, N') && alphaEquivalence(Application(M', N'), L);
        } 

        else {
        }
    }
}

lemma NonApplicationAlphaEquivalence(t1: LambdaTerm, t2: LambdaTerm)
    requires t1.Application? && alphaEquivalence(t1, t2)
    ensures t2.Application?
{ }
lemma ParallelReductionIsReflexive (t:LambdaTerm)
    ensures parallelReduction(t,t)
{
    EqualTermsAreAlphaEquilvalent(t,t);
}

lemma ParallelReductionAlphaInvariance(t1: LambdaTerm, t2: LambdaTerm, t1': LambdaTerm, t2': LambdaTerm)
    requires parallelReduction(t1, t2)
    requires alphaEquivalence(t1, t1')
    requires alphaEquivalence(t2, t2')
    ensures parallelReduction(t1', t2')
    decreases lHeight(t1), 0
{
    if alphaEquivalence(t1, t2) {
        AlphaEquivSymmetric(t1, t1');
        AlphaEquivTransitive(t1', t1, t2);
        AlphaEquivTransitive(t1', t2, t2');
        return;
    }
    match t1 {
        case Var(z) => {
            assert false;
        }
        case Lambda(x, body1) => {
            var r :| parallelReduction(body1, r) && alphaEquivalence(Lambda(x, r), t2);
            NonLambdaAlphaEquivalence(t1, t1');
            match t1' {
                case Lambda(x', body1') => {
                    ParRedAlphaUnderBinder(x, body1, r, x', body1');
                    var RR :| parallelReduction(body1', RR) && alphaEquivalence(Lambda(x', RR), Lambda(x, r));
                    AlphaEquivTransitive(Lambda(x', RR), Lambda(x, r), t2);
                    AlphaEquivTransitive(Lambda(x', RR), t2, t2');
                    ParRedLambdaIntro(x', body1', RR, t2');
                }
                case _ => {}
            }
        }
        case Application(t1a, t1b) => {
            NonApplicationAlphaEquivalence(t1, t1');
            match t1' {
                case Application(t1a', t1b') => {
                    ApplicationEquivalenceDown(t1a, t1b, t1a', t1b');
                    if t2.Application? && parallelReduction(t1a, t2.t1) && parallelReduction(t1b, t2.t2) {
                        NonApplicationAlphaEquivalence(t2, t2');
                        match t2' {
                            case Application(t2a', t2b') => {
                                ApplicationEquivalenceDown(t2.t1, t2.t2, t2a', t2b');
                                ParallelReductionAlphaInvariance(t1a, t2.t1, t1a', t2a');
                                ParallelReductionAlphaInvariance(t1b, t2.t2, t1b', t2b');
                                assert parallelReduction(t1a', t2a') && parallelReduction(t1b', t2b');
                            }
                            case _ => {}
                        }
                    } else {
                        match t1a {
                            case Lambda(x, M) => {
                                var M', N' :| parallelReduction(M, M') && parallelReduction(t1b, N')
                                              && alphaEquivalence(t2, caSubstitution(M', x, N'));
                                NonLambdaAlphaEquivalence(t1a, t1a');
                                match t1a' {
                                    case Lambda(x', body') => {
                                        ParRedAlphaUnderBinder(x, M, M', x', body');
                                        var M'' :| parallelReduction(body', M'')
                                                   && alphaEquivalence(Lambda(x', M''), Lambda(x, M'));
                                        EqualTermsAreAlphaEquilvalent(N', N');
                                        ParallelReductionAlphaInvariance(t1b, N', t1b', N');
                                        AlphaEquivSymmetric(Lambda(x', M''), Lambda(x, M'));
                                        SubstRespectsBinderAlpha(x, M', x', M'', N');
                                        AlphaEquivSymmetric(t2, t2');
                                        AlphaEquivTransitive(t2', t2, caSubstitution(M', x, N'));
                                        AlphaEquivTransitive(t2', caSubstitution(M', x, N'), caSubstitution(M'', x', N'));
                                        ParRedBetaIntro(x', body', t1b', M'', N', t2');
                                    }
                                    case _ => {}
                                }
                            }
                            case _ => {}
                        }
                    }
                }
                case _ => {}
            }
        }
    }
}

lemma NoFreeVariablesToReplace (M:LambdaTerm,x:Id,P:LambdaTerm)
    requires !(x in free(M))
    ensures alphaEquivalence(caSubstitution(M,x,P),M) 
{
    var ids:=reunion(vars(M),vars(P));
    reunionIncludesBothSets(vars(M),vars(P));
    var safe_ids:=addition(x,ids);
    NoFreeVariablesToReplace'(M,x,P,caSubstitution(M,x,P),safe_ids);
}
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
    requires x in ids
    requires M_sub==caSubstitution'(M,x,P,ids)
    ensures alphaEquivalence(M_sub,M) 
    decreases lHeight(M)
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
                    var ids_with_x:=addition(x,ids);
                    var ids' := addAnUniqueId(ids_with_x);
                    var y'   := ids'[0];
                    var vari := Var(y');
                    var M'_renamed := substitution(M', y, vari);

                        assert !(y' in ids);

                        subsitutionOfVarDoesNotChangeHeightFORVARIABLES(M', y, vari);

                        ASubLambdaOfAUniqueLambdaIsUnique(M);
                        varsOfALambdaIncludesVarsofASubLambda(M);
                        newIdsDueToSubstitution(M', y, vari, ids');

                        assert !(y' in ids);
                        assert y' != x;  

                        NotInFreeAndNotFoundInLambdaSoNotInFree(M', x, y);
                        assert !(x in free(M'));

                        SubstitutionPreservesNonFree(M', y, vari, x);
                        assert !(x in free(M'_renamed));

                        assert !(y' in ids);
                        assert includes(ids, vars(M'));
                        assert !(y' in vars(M'));

                        var M'_sub := caSubstitution'(M'_renamed, x, P, ids');
                        assert M_sub == Lambda(y', M'_sub);

                        NoFreeVariablesToReplace'(M'_renamed, x, P, M'_sub, ids');

                        AlphaCongruenceLambda(y', M'_sub, M'_renamed);

                        SubstAlphaEquivalence(M', y, y');

                        assert alphaEquivalence(Lambda(y, M'), Lambda(y', M'_renamed));

                        AlphaEquivSymmetric(Lambda(y, M'), Lambda(y', M'_renamed));
                        assert alphaEquivalence(Lambda(y', M'_renamed), Lambda(y, M'));

                        AlphaEquivTransitive(Lambda(y', M'_sub), Lambda(y', M'_renamed), Lambda(y, M'));
                        assert alphaEquivalence(M_sub, M);
                }
            }

        }
}



lemma CaSubstEquivalence (t1:LambdaTerm,t2:LambdaTerm,t1':LambdaTerm,t2':LambdaTerm,x:Id)
    requires alphaEquivalence(t1,t1') && alphaEquivalence(t2,t2')
    ensures alphaEquivalence(caSubstitution(t1,x,t2),caSubstitution(t1',x,t2'))
{
    if (!(x in free(t1)) && !(x in free(t1')))
    {
        NoFreeVariablesToReplace(t1,x,t2);
        NoFreeVariablesToReplace(t1',x,t2');
        assert alphaEquivalence(caSubstitution(t1,x,t2),t1);
        assert alphaEquivalence(caSubstitution(t1',x,t2'),t1');


        AlphaEquivSymmetric(caSubstitution(t1',x,t2'),t1');
        AlphaEquivTransitive(caSubstitution(t1,x,t2),t1,t1');

        assert alphaEquivalence(caSubstitution(t1,x,t2),t1');

        
        assert alphaEquivalence(t1',caSubstitution(t1',x,t2'));
         AlphaEquivTransitive(caSubstitution(t1,x,t2),t1',caSubstitution(t1',x,t2'));
        assert  alphaEquivalence(caSubstitution(t1,x,t2),caSubstitution(t1',x,t2'));
    }
    else
    {
        if ((x in free(t1)))
        {
            sameFreeForEquivalent(t1,t1',x);
        }
        else
        {
            assert x in free(t1');
            AlphaEquivSymmetric(t1,t1');
            sameFreeForEquivalent(t1',t1,x);
        }
        assert x in free(t1');
        assert x in free(t1);

        reunionIncludesBothSets(vars(t1),vars(t2));
        reunionIncludesBothSets(vars(t1'),vars(t2'));
        var ids1:=reunion(vars(t1),vars(t2));
        var ids2:=reunion(vars(t1'),vars(t2'));
        var safe_ids1:=addition(x,ids1);
        var safe_ids2:=addition(x,ids2);
        CaSubstEquivalence' (t1,t2,t1',t2',x,safe_ids1,safe_ids2);
    }
}
lemma sameFreeForEquivalent(t1:LambdaTerm,t2:LambdaTerm,x:Id)
    requires x in free(t1)
    requires alphaEquivalence(t1,t2)
    ensures x in free(t2)
{
    sameFreeForEquivalent'(t1,t2,x,[],[]);
}

lemma sameFreeForEquivalent'(t1:LambdaTerm, t2:LambdaTerm, x:Id, id1:seq<Id>, id2:seq<Id>)
    requires alphaEquivalence'(t1, t2, id1, id2)
    requires x in free(t1)
    requires findId(id1, x) == None
    ensures x in free(t2)
    ensures findId(id2, x) == None
    decreases minim(lHeight(t1), lHeight(t2))
{
    match t1 {
        case Var(y) => {
            match t2 {
                case Var(z) => {
                
                }
            }
        }
        case Application(t1a, t1b) => {
            match t2 {
                case Application(t2a, t2b) => {
                    if x in free(t1a) {
                        sameFreeForEquivalent'(t1a, t2a, x, id1, id2);
                    }
                    if x in free(t1b) {
                        sameFreeForEquivalent'(t1b, t2b, x, id1, id2);
                    }
                }
                case _ => assert false;
            }
        }
        case Lambda(y, t1') => {
            match t2 {
                case Lambda(z, t2') => {
                    var id1' := id1 + [y];
                    var id2' := id2 + [z];
                    
                    assert id1'[|id1'|-1] == y;
                    assert id1'[..|id1'|-1] == id1;
                    
                    sameFreeForEquivalent'(t1', t2', x, id1', id2');
                    
                    assert id2'[|id2'|-1] == z;
                    assert id2'[..|id2'|-1] == id2;
                    if x == z {
                        assert findId(id2', x) == Some(|id2'|-1);
                        assert false; 
                    }
                }
                case _ => assert false;
            }
        }
    }
}
lemma NonLambdaAlphaEquivalence(t1: LambdaTerm, t2: LambdaTerm)
    requires t1.Lambda?
    requires alphaEquivalence(t1, t2)
    ensures t2.Lambda?
{
    
}

lemma BanListWeakening(t: LambdaTerm, x: Id, t': LambdaTerm, ids_small: seq<Id>, ids_large: seq<Id>)
    requires allUnique(ids_small) && allUnique(ids_large)
    requires var s1 := vars(t); allUnique(s1) && includes(ids_small, s1)
    requires var s2 := vars(t'); allUnique(s2) && includes(ids_small, s2)
    requires var l1 := vars(t); allUnique(l1) && includes(ids_large, l1)
    requires var l2 := vars(t'); allUnique(l2) && includes(ids_large, l2)
    requires x in ids_small && x in ids_large
    ensures alphaEquivalence(caSubstitution'(t, x, t', ids_small), caSubstitution'(t, x, t', ids_large))
    decreases lHeight(t)
{
    if x in free(t) {
        EqualTermsAreAlphaEquilvalent(t, t);
        EqualTermsAreAlphaEquilvalent(t', t');
        CaSubstEquivalence'(t, t', t, t', x, ids_small, ids_large);
    } else {
        var sub_small := caSubstitution'(t, x, t', ids_small);
        var sub_large := caSubstitution'(t, x, t', ids_large);
        NoFreeVariablesToReplace'(t, x, t', sub_small, ids_small);
        NoFreeVariablesToReplace'(t, x, t', sub_large, ids_large);
        AlphaEquivSymmetric(sub_large, t);
        AlphaEquivTransitive(sub_small, t, sub_large);
    }
}

lemma SubstDistributesOverApp(M1: LambdaTerm, M2: LambdaTerm, x: Id, N: LambdaTerm)
    ensures alphaEquivalence(
        caSubstitution(Application(M1, M2), x, N),
        Application(caSubstitution(M1, x, N), caSubstitution(M2, x, N))
    )
{
    var M := Application(M1, M2);
    varsOfALambdaIncludesVarsofASubLambda(M);
    
    var ids_global := addition(x, reunion(vars(M), vars(N)));
    reunionIncludesBothSets(vars(M), vars(N));
    
    var left_M1 := caSubstitution'(M1, x, N, ids_global);
    var left_M2 := caSubstitution'(M2, x, N, ids_global);
    var left_result := Application(left_M1, left_M2);
    assert caSubstitution(M, x, N) == left_result;

    var ids_M1 := addition(x, reunion(vars(M1), vars(N)));
    reunionIncludesBothSets(vars(M1), vars(N));
    var right_M1 := caSubstitution'(M1, x, N, ids_M1);
    
    var ids_M2 := addition(x, reunion(vars(M2), vars(N)));
    reunionIncludesBothSets(vars(M2), vars(N));
    var right_M2 := caSubstitution'(M2, x, N, ids_M2);
    
    var right_result := Application(right_M1, right_M2);
    assert Application(caSubstitution(M1, x, N), caSubstitution(M2, x, N)) == right_result;

    BanListWeakening(M1, x, N, ids_M1, ids_global);
    AlphaEquivSymmetric(right_M1, left_M1); 

    BanListWeakening(M2, x, N, ids_M2, ids_global);
    AlphaEquivSymmetric(right_M2, left_M2); 
    ApplicationEquivalence(left_M1, right_M1, left_M2, right_M2);
}

lemma SubstPushesIntoSafeLambda(z: Id, M: LambdaTerm, x: Id, N: LambdaTerm)
    requires x != z
    requires !(z in free(N))
    ensures alphaEquivalence(
        caSubstitution(Lambda(z, M), x, N),
        Lambda(z, caSubstitution(M, x, N))
    )
{
    var parent := Lambda(z, M);
    varsOfALambdaIncludesVarsofASubLambda(parent);
    
    var ids_global := addition(x, reunion(vars(parent), vars(N)));
    reunionIncludesBothSets(vars(parent), vars(N));

    var left_inner := caSubstitution'(M, x, N, ids_global);
    var left_result := Lambda(z, left_inner);
    assert caSubstitution(parent, x, N) == left_result;

    var ids_local := addition(x, reunion(vars(M), vars(N)));
    reunionIncludesBothSets(vars(M), vars(N));
    var right_inner := caSubstitution'(M, x, N, ids_local);
    var right_result := Lambda(z, right_inner);
    assert Lambda(z, caSubstitution(M, x, N)) == right_result;

    reunionIncludesBothSets(vars(parent), vars(N));
    reunionIncludesBothSets(vars(M), vars(N));

        forall i: nat | i < |ids_local| ensures exists j: nat :: j < |ids_global| && ids_global[j] == ids_local[i] {
            var elem := ids_local[i];
            if elem == x {
                assert elem in ids_global;
            } else {
                assert elem in vars(M) || elem in vars(N);
                if elem in vars(M) {
                    assert elem in vars(parent); 
                    assert elem in reunion(vars(parent), vars(N)); 
                    assert elem in ids_global;
                } else {
                    assert elem in vars(N);
                    assert elem in reunion(vars(parent), vars(N));
                    assert elem in ids_global;
                }
            }
        }
    
    assert includes(ids_global, ids_local);

    BanListWeakening(M, x, N, ids_local, ids_global);
    
    AlphaEquivSymmetric(right_inner, left_inner);
    
    AlphaCongruenceLambda(z, left_inner, right_inner);
}

lemma TheFreeOfCaSub(M:LambdaTerm,x:Id,N:LambdaTerm,y:Id)
    requires !(y in free(M)) && !(y in free(N)) && x!=y
    ensures !(y in free(caSubstitution(M,x,N)))
{
    reunionIncludesBothSets(vars(M),vars(N));
    var safe_ids:=addition(x,reunion(vars(M),vars(N)));
    TheFreeOfCaSub'(M,x,N,y,safe_ids);
}

lemma TheFreeOfCaSub'(M:LambdaTerm,x:Id,N:LambdaTerm,y:Id,ids:seq<Id>)
    requires !(y in free(M)) && !(y in free(N)) && x!=y
     requires allUnique(ids)
        requires var s1:=vars(M);
         allUnique(s1) && includes(ids,s1)
    requires var s2:=vars(N);
         allUnique(s2)  && includes(ids,s2)
    requires x in ids
    ensures !(y in free(caSubstitution'(M,x,N,ids)))
    decreases lHeight(M)
{
    match M 
        case Var(z) =>
        {
            if z==x
            {
                assert caSubstitution'(M,x,N,ids)==N;
                assert !(y in free(N));
            }
            else 
            {
                assert caSubstitution'(M,x,N,ids)==M;
                assert !(y in free(M));
            }
        }
        case Lambda(z,body) =>
        {
            if (z==x)
            {
                assert !(y in free(M)); 
            }
            else 
            {
                if !(z in free(N))
                {
                    varsOfALambdaIncludesVarsofASubLambda (M);
                    if (y!=z)
                    {
                        assert !(y in free(body));
                        TheFreeOfCaSub'(body,x,N,y,ids);
                        assert caSubstitution'(M,x,N,ids)==Lambda(z,caSubstitution'(body,x,N,ids));
                    }
                    else 
                    {
                         assert caSubstitution'(M,x,N,ids)==Lambda(z,caSubstitution'(body,x,N,ids));
                         assert y==z;
                         assert !(y in free(Lambda(z,caSubstitution'(body,x,N,ids))));
                    }
                }
                else
                {
                    var ids':=addAnUniqueId(ids);
                    var vari:=Var(ids'[0]);
                    var new_body:=substitution(body,z,vari);
                    subsitutionOfVarDoesNotChangeHeightFORVARIABLES(body,z,vari);
                    varsOfALambdaIncludesVarsofASubLambda (M);
                    newIdsDueToSubstitution(body,z,vari,ids');
                    assert caSubstitution'(M,x,N,ids)==Lambda(ids'[0],caSubstitution'(new_body,x,N,ids'));
                    if (ids'[0]==y)
                    {
                        assert !(y in free(Lambda(ids'[0],caSubstitution'(new_body,x,N,ids'))));
                    }
                    else 
                    {
                        assert y != ids'[0];
                        assert !(y in free(body));
                        assert vari==Var(ids'[0]);
                        SubstitutionPreservesNonFree(body,z,vari,y);

                        assert !(y in free(new_body));
                        TheFreeOfCaSub'(new_body,x,N,y,ids');

                        assert !(y in free(caSubstitution'(new_body,x,N,ids'))); 
                        assert !(y in free(Lambda(ids'[0],caSubstitution'(new_body,x,N,ids'))));
                    }
                }
            }
        }
        case Application(M1,M2) =>
        {
            assert !(y in free(M1));
            assert !(y in free(M2));
            varsOfALambdaIncludesVarsofASubLambda (M);
            TheFreeOfCaSub'(M1,x,N,y,ids);
            TheFreeOfCaSub'(M1,x,N,y,ids);
            assert caSubstitution'(M,x,N,ids)==Application(caSubstitution'(M1,x,N,ids),caSubstitution'(M2,x,N,ids));
        }

}
lemma CaSubstEquivalence'(t1:LambdaTerm,t2:LambdaTerm,t1':LambdaTerm,t2':LambdaTerm,x:Id,ids:seq<Id>,ids':seq<Id>)
    requires alphaEquivalence(t1,t1') && alphaEquivalence(t2,t2')
    requires (x in free(t1)) && (x in free(t1'))
    requires allUnique(ids)
        requires var s1:=vars(t1);
         allUnique(s1) && includes(ids,s1)
    requires var s2:=vars(t2);
         allUnique(s2)  && includes(ids,s2)

    requires allUnique(ids')
        requires var s1:=vars(t1');
         allUnique(s1) && includes(ids',s1)
    requires var s2:=vars(t2');
         allUnique(s2)  && includes(ids',s2)
    requires x in ids
    requires x in ids'
    ensures alphaEquivalence(caSubstitution'(t1,x,t2,ids),caSubstitution'(t1',x,t2',ids'))
    decreases lHeight(t1)
{
    match t1 
        case Var(y) =>
        {
            assert free(t1)=={y}; 
            assert x==y;
            var subst:=caSubstitution'(t1,x,t2,ids);
            assert subst==t2;
            EqualTermsAreAlphaEquilvalent(t2,subst);
            match t1'
                case Var(y') =>
                {
                    assert free(t1')=={y'};
                    assert x==y';
                    var subst':=caSubstitution'(t1',x,t2',ids);
                    assert caSubstitution'(t1',x,t2',ids)==t2';
                    EqualTermsAreAlphaEquilvalent(subst',t2');
                    AlphaEquivSymmetric(t2,t2');
                    AlphaEquivTransitive(subst',t2',t2);
                    AlphaEquivTransitive(subst',t2,subst);
                    AlphaEquivSymmetric(subst',subst);
                    assert alphaEquivalence(subst,subst');
                }
        }
        case Lambda(y,body1) =>
        {
            assert x!=y;
            match t1'
            case Lambda(y', body1') =>
                {
                    assert x != y'; 

                    var sub1: LambdaTerm;
                    if !(y in free(t2)) {
                        sub1 := Lambda(y, caSubstitution'(body1, x, t2, ids));
                    } else {
                        var ids_new := addAnUniqueId(ids);
                        var vari := Var(ids_new[0]);
                        SubstAlphaEquivalence(t1,x,ids_new[0]);
                        var body1_sub := substitution(body1, y, vari);
                        
                        subsitutionOfVarDoesNotChangeHeightFORVARIABLES(body1, y, vari);
                        varsOfALambdaIncludesVarsofASubLambda(t1);
                        newIdsDueToSubstitution(body1, y, vari, ids_new);

                        
                        sub1 := Lambda(ids_new[0], caSubstitution'(body1_sub, x, t2, ids_new));
                        
                    }

                    var sub2: LambdaTerm;
                    if !(y' in free(t2')) {
                        sub2 := Lambda(y', caSubstitution'(body1', x, t2', ids'));
                    } else {
                        var ids'_new := addAnUniqueId(ids');
                        var vari' := Var(ids'_new[0]);
                        var body1'_sub := substitution(body1', y', vari');
                        
                        subsitutionOfVarDoesNotChangeHeightFORVARIABLES(body1', y', vari');
                        varsOfALambdaIncludesVarsofASubLambda(t1');
                        newIdsDueToSubstitution(body1', y', vari', ids'_new);

                        sub2 := Lambda(ids'_new[0], caSubstitution'(body1'_sub, x, t2', ids'_new));
                    }

                    assert caSubstitution'(t1, x, t2, ids) == sub1;
                    assert caSubstitution'(t1', x, t2', ids') == sub2;


                    CaSubstPrimeRespectsAlpha(t1, t2, t1', t2', x, ids, ids');

                    assert alphaEquivalence(caSubstitution'(t1, x, t2, ids), caSubstitution'(t1', x, t2', ids'));
                }
        } 
        case Application(left1,right1)=>
        {
           match t1' 
                case Application(left1', right1') =>
                {
                    assert alphaEquivalence(left1, left1') && alphaEquivalence(right1, right1');

                    varsOfALambdaIncludesVarsofASubLambda(t1);
                    varsOfALambdaIncludesVarsofASubLambda(t1');

                    var subLeft1 := caSubstitution'(left1, x, t2, ids);
                    var subLeft1' := caSubstitution'(left1', x, t2', ids');
                    var subRight1 := caSubstitution'(right1, x, t2, ids);
                    var subRight1' := caSubstitution'(right1', x, t2', ids');


                    if x in free(left1) {
                        sameFreeForEquivalent(left1, left1', x);
                        CaSubstEquivalence'(left1, t2, left1', t2', x, ids, ids');
                    } else {

                        if x in free(left1') {
                            AlphaEquivSymmetric(left1, left1');
                            sameFreeForEquivalent(left1', left1, x);
                            assert false;
                        }
                        
                        NoFreeVariablesToReplace'(left1, x, t2, subLeft1, ids);
                        NoFreeVariablesToReplace'(left1', x, t2', subLeft1', ids');
                        
                        AlphaEquivTransitive(subLeft1, left1, left1');
                        AlphaEquivSymmetric(subLeft1', left1');
                        AlphaEquivTransitive(subLeft1, left1', subLeft1');
                    }

                    if x in free(right1) {
                        sameFreeForEquivalent(right1, right1', x);
                        CaSubstEquivalence'(right1, t2, right1', t2', x, ids, ids');
                    } else {

                        if x in free(right1') {
                            AlphaEquivSymmetric(right1, right1');
                            sameFreeForEquivalent(right1', right1, x);
                            assert false;
                        }

                        NoFreeVariablesToReplace'(right1, x, t2, subRight1, ids);
                        NoFreeVariablesToReplace'(right1', x, t2', subRight1', ids');
                        
                        AlphaEquivTransitive(subRight1, right1, right1');
                        AlphaEquivSymmetric(subRight1', right1');
                        AlphaEquivTransitive(subRight1, right1', subRight1');
                    }

                    assert caSubstitution'(t1, x, t2, ids) == Application(subLeft1, subRight1);
                    assert caSubstitution'(t1', x, t2', ids') == Application(subLeft1', subRight1');

                    ApplicationEquivalence(subLeft1, subLeft1', subRight1, subRight1');
                }
        }
}


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

lemma getVarCaSubstitution(M:LambdaTerm,x:Id,N:LambdaTerm)
    requires M.Var?
    ensures (match M 
            case Var(y) => ( if y==x then caSubstitution(M,x,N)==N else caSubstitution(M,x,N)==M ))
{
    var ids:=reunion(vars(M),vars(N));
    reunionIncludesBothSets(vars(M),vars(N));
    var safe_ids := addition(x, ids);
    var sub_M:=caSubstitution'(M,x,N,safe_ids);
    assert sub_M==caSubstitution(M,x,N);
    match M
        case Var(y) =>
        {
            if (y==x)
            {
                assert sub_M==N;
            }
            else 
            {
                assert sub_M==M;
            }
        }
        case _ =>
        {
            assert false;
        }
}

lemma notInVarsSoNotInFree(t:LambdaTerm,x:Id)
    requires !(x in vars(t))
    ensures !(x in free(t))
{

}

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















// Removing a common OUTERMOST binder preserves alpha (inverse of AlphaCongruenceLambda').
lemma StripOuterBinder(t1:LambdaTerm, t2:LambdaTerm, w:Id, id1:seq<Id>, id2:seq<Id>)
    requires alphaEquivalence'(t1, t2, [w]+id1, [w]+id2)
    ensures alphaEquivalence'(t1, t2, id1, id2)
    decreases minim(lHeight(t1), lHeight(t2))
                {
    match t1 {
        case Var(x) => {
            var z :| t2 == Var(z);
            findId_prepend(id1, x, w);
            findId_prepend(id2, z, w);
        }
        case Lambda(x, t1b) => {
            var z, t2b :| t2 == Lambda(z, t2b);
            assert ([w]+id1)+[x] == [w]+(id1+[x]);
            assert ([w]+id2)+[z] == [w]+(id2+[z]);
            StripOuterBinder(t1b, t2b, w, id1+[x], id2+[z]);
        }
        case Application(t1a, t1b) => {
            var t2a, t2b :| t2 == Application(t2a, t2b);
            StripOuterBinder(t1a, t2a, w, id1, id2);
            StripOuterBinder(t1b, t2b, w, id1, id2);
        }
    }
}

lemma StripSameBinder(w:Id, a:LambdaTerm, b:LambdaTerm)
    requires alphaEquivalence(Lambda(w,a), Lambda(w,b))
    ensures alphaEquivalence(a, b)
{
    assert []+[w] == [w];
    assert [w] == [w]+[];
    StripOuterBinder(a, b, w, [], []);
}

lemma FreeSubsetVars(t:LambdaTerm)
    ensures forall i:Id :: i in free(t) ==> i in vars(t)
{
    match t {
        case Var(_) => { }
        case Lambda(y,b) => { FreeSubsetVars(b); varsOfALambdaIncludesVarsofASubLambda(t); }
        case Application(a,b) => { FreeSubsetVars(a); FreeSubsetVars(b); varsOfALambdaIncludesVarsofASubLambda(t); }
    }
}

lemma CaSubstPrimeIsNaiveWhenFresh(M:LambdaTerm, x:Id, w:Id, ids:seq<Id>)
    requires allUnique(ids)
    requires includes(ids, vars(M))
    requires w in ids
    requires x in ids
    requires !(w in vars(M))
    ensures caSubstitution'(M, x, Var(w), ids) == substitution(M, x, Var(w))
    decreases lHeight(M)
{
    match M {
        case Var(y) => { }
        case Application(a, b) => {
            varsOfALambdaIncludesVarsofASubLambda(M);
            CaSubstPrimeIsNaiveWhenFresh(a, x, w, ids);
            CaSubstPrimeIsNaiveWhenFresh(b, x, w, ids);
        }
        case Lambda(z, P) => {
            if z == x {
            } else {
                varsOfALambdaIncludesVarsofASubLambda(M);
                assert z in vars(M);
                assert w != z;
                assert !(z in free(Var(w)));
                assert !(w in vars(P));
                CaSubstPrimeIsNaiveWhenFresh(P, x, w, ids);
            }
        }
    }
}

lemma CaSubstIsNaiveWhenFresh(M:LambdaTerm, x:Id, w:Id)
    requires !(w in vars(M))
    ensures caSubstitution(M, x, Var(w)) == substitution(M, x, Var(w))
{
    var ids := reunion(vars(M), vars(Var(w)));
    reunionIncludesBothSets(vars(M), vars(Var(w)));
    var safe_ids := addition(x, ids);
    CaSubstPrimeIsNaiveWhenFresh(M, x, w, safe_ids);
}

// Commutation of two naive variable-renamings (all four names distinct).
lemma SubstSubstSwapVars(P:LambdaTerm, x:Id, w:Id, z:Id, zz:Id)
    requires x != w && x != z && x != zz && w != z && w != zz && z != zz
    ensures substitution(substitution(P,x,Var(w)), z, Var(zz))
         == substitution(substitution(P,z,Var(zz)), x, Var(w))
    decreases lHeight(P)
{
    match P {
        case Var(u) => { }
        case Application(a,b) => {
            SubstSubstSwapVars(a,x,w,z,zz);
            SubstSubstSwapVars(b,x,w,z,zz);
        }
        case Lambda(u,Q) => {
            if u == x {
            } else if u == z {
            } else {
                SubstSubstSwapVars(Q,x,w,z,zz);
            }
        }
    }
}


lemma {:vcs_split_on_every_assert} RenameThenSubstCapture(z:Id, P:LambdaTerm, x:Id, w:Id, N:LambdaTerm)
    requires !(w in vars(P))
    requires x != w && z != w && z != x
    requires z in free(N)
    ensures alphaEquivalence(caSubstitution(substitution(Lambda(z,P),x,Var(w)), w, N),
                             caSubstitution(Lambda(z,P), x, N))
    decreases lHeight(Lambda(z,P)), 0
{
    var A := Lambda(z,P);
    var sP := substitution(P,x,Var(w));
    assert substitution(A,x,Var(w)) == Lambda(z, sP);

    var s2 := addition(x, addition(z, addition(w, reunion(vars(P), vars(N)))));
    reunionIncludesBothSets(vars(P), vars(N));
    var zz := addAnUniqueId(s2)[0];
    assert !(zz in s2);
    assert zz != x && zz != z && zz != w;
    assert !(zz in vars(P)) && !(zz in vars(N));
    FreeSubsetVars(N);
    assert !(zz in free(N));

    var idsP := addition(w, vars(P));
    assert includes(idsP, vars(P));
    newIdsDueToSubstitution(P, x, Var(w), idsP);
    assert includes(idsP, vars(sP));
    assert !(zz in idsP);
    assert !(zz in vars(sP));

    var Pzz := substitution(P, z, Var(zz));
    var sPzz := substitution(sP, z, Var(zz));

    SubstSubstSwapVars(P, x, w, z, zz);
    assert sPzz == substitution(Pzz, x, Var(w));

    SubstAlphaEquivalence(P, z, zz);
    SubstAlphaEquivalence(sP, z, zz);

    EqualTermsAreAlphaEquilvalent(N, N);
    CaSubstEquivalence(Lambda(z,P), N, Lambda(zz,Pzz), N, x);
    SubstPushesIntoSafeLambda(zz, Pzz, x, N);
    var R := caSubstitution(A, x, N);
    AlphaEquivTransitive(R, caSubstitution(Lambda(zz,Pzz),x,N), Lambda(zz, caSubstitution(Pzz,x,N)));

    CaSubstEquivalence(Lambda(z,sP), N, Lambda(zz,sPzz), N, w);
    SubstPushesIntoSafeLambda(zz, sPzz, w, N);
    var L := caSubstitution(Lambda(z,sP), w, N);
    AlphaEquivTransitive(L, caSubstitution(Lambda(zz,sPzz),w,N), Lambda(zz, caSubstitution(sPzz,w,N)));

    var idsW := addition(zz, vars(P));
    assert includes(idsW, vars(P));
    newIdsDueToSubstitution(P, z, Var(zz), idsW);
    assert includes(idsW, vars(Pzz));
    assert !(w in idsW);
    assert !(w in vars(Pzz));

    subsitutionOfVarDoesNotChangeHeightFORVARIABLES(P, z, Var(zz));
    RenameThenSubst(Pzz, x, w, N);
    assert caSubstitution(sPzz,w,N) == caSubstitution(substitution(Pzz,x,Var(w)),w,N);
    AlphaCongruenceLambda(zz, caSubstitution(sPzz,w,N), caSubstitution(Pzz,x,N));

    AlphaEquivTransitive(L, Lambda(zz, caSubstitution(sPzz,w,N)), Lambda(zz, caSubstitution(Pzz,x,N)));
    AlphaEquivSymmetric(R, Lambda(zz, caSubstitution(Pzz,x,N)));
    AlphaEquivTransitive(L, Lambda(zz, caSubstitution(Pzz,x,N)), R);
}

lemma {:vcs_split_on_every_assert} RenameThenSubst(A:LambdaTerm, x:Id, w:Id, N:LambdaTerm)
    requires !(w in vars(A))
    requires x != w
    ensures alphaEquivalence(caSubstitution(substitution(A,x,Var(w)), w, N),
                             caSubstitution(A,x,N))
    decreases lHeight(A), 1
{
    match A {
        case Var(y) => {
            if y == x {
                getVarCaSubstitution(Var(w), w, N);
                getVarCaSubstitution(Var(x), x, N);
                EqualTermsAreAlphaEquilvalent(caSubstitution(substitution(A,x,Var(w)),w,N), caSubstitution(A,x,N));
            } else {
                assert y != w;
                getVarCaSubstitution(Var(y), w, N);
                getVarCaSubstitution(Var(y), x, N);
                EqualTermsAreAlphaEquilvalent(caSubstitution(substitution(A,x,Var(w)),w,N), caSubstitution(A,x,N));
            }
        }
        case Application(a,b) => {
            varsOfALambdaIncludesVarsofASubLambda(A);
            assert !(w in vars(a)) && !(w in vars(b));
            var sa := substitution(a,x,Var(w));
            var sb := substitution(b,x,Var(w));
            assert substitution(A,x,Var(w)) == Application(sa, sb);

            SubstDistributesOverApp(sa, sb, w, N);
            SubstDistributesOverApp(a, b, x, N);

            RenameThenSubst(a,x,w,N);
            RenameThenSubst(b,x,w,N);

            ApplicationEquivalence(caSubstitution(sa,w,N), caSubstitution(a,x,N),
                                   caSubstitution(sb,w,N), caSubstitution(b,x,N));
            var L := caSubstitution(substitution(A,x,Var(w)),w,N);
            var R := caSubstitution(A,x,N);
            AlphaEquivSymmetric(R, Application(caSubstitution(a,x,N), caSubstitution(b,x,N)));
            AlphaEquivTransitive(L, Application(caSubstitution(sa,w,N), caSubstitution(sb,w,N)),
                                    Application(caSubstitution(a,x,N), caSubstitution(b,x,N)));
            AlphaEquivTransitive(L, Application(caSubstitution(a,x,N), caSubstitution(b,x,N)), R);
        }
        case Lambda(z,P) => {
            varsOfALambdaIncludesVarsofASubLambda(A);
            assert z in vars(A) && z != w;
            assert !(w in vars(P));
            if z == x {
                assert substitution(A,x,Var(w)) == A;
                FreeSubsetVars(A);
                assert !(w in free(A));
                NoFreeVariablesToReplace(A, w, N);
                LambdaNullifiesSubstitution(P, x, N);
                AlphaEquivSymmetric(caSubstitution(A,w,N), A);
                EqualTermsAreAlphaEquilvalent(A, caSubstitution(A,x,N));
                AlphaEquivTransitive(caSubstitution(A,w,N), A, caSubstitution(A,x,N));
            } else {
                var sP := substitution(P,x,Var(w));
                assert substitution(A,x,Var(w)) == Lambda(z, sP);
                if !(z in free(N)) {
                    SubstPushesIntoSafeLambda(z, sP, w, N);
                    SubstPushesIntoSafeLambda(z, P, x, N);
                    RenameThenSubst(P,x,w,N);
                    AlphaCongruenceLambda(z, caSubstitution(sP,w,N), caSubstitution(P,x,N));

                    var L := caSubstitution(Lambda(z,sP), w, N);
                    var R := caSubstitution(A, x, N);
                    AlphaEquivTransitive(L, Lambda(z, caSubstitution(sP,w,N)), Lambda(z, caSubstitution(P,x,N)));
                    AlphaEquivSymmetric(R, Lambda(z, caSubstitution(P,x,N)));
                    AlphaEquivTransitive(L, Lambda(z, caSubstitution(P,x,N)), R);
                } else {
                    RenameThenSubstCapture(z, P, x, w, N);
                }
            }
        }
    }
}


lemma SubstRespectsBinderAlpha(x:Id, A:LambdaTerm, xx:Id, B:LambdaTerm, N:LambdaTerm)
    requires alphaEquivalence(Lambda(x,A), Lambda(xx,B))
    ensures alphaEquivalence(caSubstitution(A,x,N), caSubstitution(B,xx,N))
{
    reunionIncludesBothSets(vars(B), vars(N));
    var inner := reunion(vars(B), vars(N));
    var s := addition(x, addition(xx, reunion(vars(A), inner)));
    var w := addAnUniqueId(s)[0];
    assert !(w in s);
    assert w != x && w != xx;
    reunionIncludesBothSets(vars(A), inner);
    assert !(w in vars(A)) && !(w in vars(B)) && !(w in vars(N));

    var Aw := substitution(A, x, Var(w));
    var Bw := substitution(B, xx, Var(w));

    SubstAlphaEquivalence(A, x, w);
    SubstAlphaEquivalence(B, xx, w);
    AlphaEquivSymmetric(Lambda(x,A), Lambda(w,Aw));
    AlphaEquivTransitive(Lambda(w,Aw), Lambda(x,A), Lambda(xx,B));
    AlphaEquivTransitive(Lambda(w,Aw), Lambda(xx,B), Lambda(w,Bw));
    StripSameBinder(w, Aw, Bw);

                    EqualTermsAreAlphaEquilvalent(N, N);
    CaSubstEquivalence(Aw, N, Bw, N, w);

    RenameThenSubst(A, x, w, N);
    RenameThenSubst(B, xx, w, N);

    AlphaEquivSymmetric(caSubstitution(Aw,w,N), caSubstitution(A,x,N));
    AlphaEquivTransitive(caSubstitution(A,x,N), caSubstitution(Aw,w,N), caSubstitution(Bw,w,N));
    AlphaEquivTransitive(caSubstitution(A,x,N), caSubstitution(Bw,w,N), caSubstitution(B,xx,N));
                }


// ===========================================================================
// Mutually-recursive layer for alpha-invariance of parallel reduction.
// ===========================================================================

lemma AlphaSameHeight'(t1:LambdaTerm, t2:LambdaTerm, id1:seq<Id>, id2:seq<Id>)
    requires alphaEquivalence'(t1, t2, id1, id2)
    ensures lHeight(t1) == lHeight(t2)
    decreases lHeight(t1)
{
    match t1 {
        case Var(_) => { }
        case Lambda(x, b) => {
            var y, b2 :| t2 == Lambda(y, b2);
            AlphaSameHeight'(b, b2, id1+[x], id2+[y]);
        }
        case Application(a, b) => {
            var a2, b2 :| t2 == Application(a2, b2);
            AlphaSameHeight'(a, a2, id1, id2);
            AlphaSameHeight'(b, b2, id1, id2);
        }
    }
}
lemma AlphaSameHeight(t1:LambdaTerm, t2:LambdaTerm)
    requires alphaEquivalence(t1, t2)
    ensures lHeight(t1) == lHeight(t2)
{ AlphaSameHeight'(t1, t2, [], []); }

lemma BinderRenameNotFree(x:Id, B:LambdaTerm, x':Id, B':LambdaTerm)
    requires alphaEquivalence(Lambda(x,B), Lambda(x',B'))
    requires x != x'
    ensures !(x' in free(B))
{
    if x' in free(B) {
        assert x' in free(Lambda(x,B));
        sameFreeForEquivalent(Lambda(x,B), Lambda(x',B'), x');
        assert false;
    }
}

lemma NaiveSubstRemovesVar(t:LambdaTerm, v:Id, zf:Id)
    requires v != zf
    ensures !(v in free(substitution(t, v, Var(zf))))
    decreases lHeight(t)
{
    match t {
        case Var(y) => { }
        case Lambda(w, b) => { if w == v { } else { NaiveSubstRemovesVar(b, v, zf); } }
        case Application(a, b) => { NaiveSubstRemovesVar(a, v, zf); NaiveSubstRemovesVar(b, v, zf); }
    }
}

lemma SubstedVarNotFree'(P:LambdaTerm, z:Id, Q:LambdaTerm, ids:seq<Id>)
    requires allUnique(ids)
    requires includes(ids, vars(P)) && includes(ids, vars(Q)) && z in ids
    requires !(z in free(Q))
    ensures !(z in free(caSubstitution'(P, z, Q, ids)))
    decreases lHeight(P)
{
    match P {
        case Var(y) => { }
        case Lambda(w, body) => {
            if w == z {
            } else if !(w in free(Q)) {
                varsOfALambdaIncludesVarsofASubLambda(P);
                SubstedVarNotFree'(body, z, Q, ids);
            } else {
                var ids' := addAnUniqueId(ids);
                var vari := Var(ids'[0]);
                var nb := substitution(body, w, vari);
                subsitutionOfVarDoesNotChangeHeightFORVARIABLES(body, w, vari);
                varsOfALambdaIncludesVarsofASubLambda(P);
                newIdsDueToSubstitution(body, w, vari, ids');
                SubstedVarNotFree'(nb, z, Q, ids');
            }
        }
        case Application(P1, P2) => {
            varsOfALambdaIncludesVarsofASubLambda(P);
            SubstedVarNotFree'(P1, z, Q, ids);
            SubstedVarNotFree'(P2, z, Q, ids);
        }
    }
}
lemma SubstedVarNotFree(P:LambdaTerm, z:Id, Q:LambdaTerm)
    requires !(z in free(Q))
    ensures !(z in free(caSubstitution(P, z, Q)))
{
    var ids := reunion(vars(P), vars(Q));
    reunionIncludesBothSets(vars(P), vars(Q));
    var safe := addition(z, ids);
    SubstedVarNotFree'(P, z, Q, safe);
}

lemma ParRedPreservesNonFree(M:LambdaTerm, M':LambdaTerm, y:Id)
    requires parallelReduction(M, M')
    requires !(y in free(M))
    ensures !(y in free(M'))
    decreases lHeight(M)
{
    if alphaEquivalence(M, M') {
        if y in free(M') { AlphaEquivSymmetric(M, M'); sameFreeForEquivalent(M', M, y); }
    } else {
        match M {
            case Var(_) => { }
            case Lambda(x, body) => {
                var r :| parallelReduction(body, r) && alphaEquivalence(Lambda(x, r), M');
                if y != x { ParRedPreservesNonFree(body, r, y); }
                assert !(y in free(Lambda(x, r)));
                if y in free(M') {
                    AlphaEquivSymmetric(Lambda(x, r), M');
                    sameFreeForEquivalent(M', Lambda(x, r), y);
                }
            }
            case Application(P, Q) => {
                if M'.Application? && parallelReduction(P, M'.t1) && parallelReduction(Q, M'.t2) {
                    ParRedPreservesNonFree(P, M'.t1, y);
                    ParRedPreservesNonFree(Q, M'.t2, y);
                } else {
                    match P {
                        case Lambda(z, Pb) => {
                            var Pb', Q' :| parallelReduction(Pb, Pb') && parallelReduction(Q, Q')
                                           && alphaEquivalence(M', caSubstitution(Pb', z, Q'));
                            assert !(y in free(Q));
                            ParRedPreservesNonFree(Q, Q', y);
                            if y == z {
                                SubstedVarNotFree(Pb', z, Q');
                            } else {
                                assert !(y in free(Pb));
                                ParRedPreservesNonFree(Pb, Pb', y);
                                TheFreeOfCaSub(Pb', z, Q', y);
                            }
                            assert !(y in free(caSubstitution(Pb', z, Q')));
                            if y in free(M') {
                                sameFreeForEquivalent(M', caSubstitution(Pb', z, Q'), y);
                            }
                        }
                        case _ => { assert false; }
                    }
                }
            }
        }
    }
}

lemma AvoidVarInTerm(M:LambdaTerm, v:Id)
    requires !(v in free(M))
    ensures exists M' :: alphaEquivalence(M, M') && !(v in vars(M'))
    decreases lHeight(M)
{
    match M {
        case Var(y) => { EqualTermsAreAlphaEquilvalent(M, M); }
        case Application(P, Q) => {
            AvoidVarInTerm(P, v);
            var P' :| alphaEquivalence(P, P') && !(v in vars(P'));
            AvoidVarInTerm(Q, v);
            var Q' :| alphaEquivalence(Q, Q') && !(v in vars(Q'));
            ApplicationEquivalence(P, P', Q, Q');
            reunionIncludesBothSets(vars(P'), vars(Q'));
            assert !(v in vars(Application(P', Q')));
        }
        case Lambda(z, body) => {
            varsOfALambdaIncludesVarsofASubLambda(M);
            if z == v {
                var zf := addAnUniqueId(vars(M))[0];
                assert !(zf in vars(M)) && !(zf in vars(body));
                var br := substitution(body, v, Var(zf));
                SubstAlphaEquivalence(body, v, zf);
                subsitutionOfVarDoesNotChangeHeightFORVARIABLES(body, v, Var(zf));
                NaiveSubstRemovesVar(body, v, zf);
                AvoidVarInTerm(br, v);
                var br2 :| alphaEquivalence(br, br2) && !(v in vars(br2));
                AlphaCongruenceLambda(zf, br, br2);
                AlphaEquivTransitive(M, Lambda(zf, br), Lambda(zf, br2));
                assert !(v in vars(Lambda(zf, br2)));
            } else {
                assert !(v in free(body));
                AvoidVarInTerm(body, v);
                var body2 :| alphaEquivalence(body, body2) && !(v in vars(body2));
                AlphaCongruenceLambda(z, body, body2);
                assert !(v in vars(Lambda(z, body2)));
            }
        }
    }
}

lemma ParRedLambdaIntro(zf:Id, body:LambdaTerm, rr:LambdaTerm, t2:LambdaTerm)
    requires parallelReduction(body, rr) && alphaEquivalence(Lambda(zf, rr), t2)
    ensures parallelReduction(Lambda(zf, body), t2)
{ }
lemma ParRedBetaIntro(zf:Id, PbA:LambdaTerm, QA:LambdaTerm, P2:LambdaTerm, N2:LambdaTerm, t2:LambdaTerm)
    requires parallelReduction(PbA, P2) && parallelReduction(QA, N2)
    requires alphaEquivalence(t2, caSubstitution(P2, zf, N2))
    ensures parallelReduction(Application(Lambda(zf, PbA), QA), t2)
{ }
lemma ParRedCongIntro(PA:LambdaTerm, QA:LambdaTerm, PpA:LambdaTerm, QpA:LambdaTerm)
    requires parallelReduction(PA, PpA) && parallelReduction(QA, QpA)
    ensures parallelReduction(Application(PA, QA), Application(PpA, QpA))
{ }

lemma {:vcs_split_on_every_assert} ParRedRename(M:LambdaTerm, M':LambdaTerm, a:Id, b:Id)
    requires parallelReduction(M, M')
    ensures parallelReduction(caSubstitution(M, a, Var(b)), caSubstitution(M', a, Var(b)))
    decreases lHeight(M), 1
{
    var Mca := caSubstitution(M, a, Var(b));
    var M'ca := caSubstitution(M', a, Var(b));
    if alphaEquivalence(M, M') {
        EqualTermsAreAlphaEquilvalent(Var(b), Var(b));
        CaSubstEquivalence(M, Var(b), M', Var(b), a);
        return;
    }
    match M {
        case Var(z) => { assert false; }
        case Lambda(z, body) => {
            var s :| parallelReduction(body, s) && alphaEquivalence(Lambda(z, s), M');
            var S := addition(a, addition(b, reunion(vars(M), reunion(vars(M'), vars(s)))));
            reunionIncludesBothSets(vars(M'), vars(s));
            reunionIncludesBothSets(vars(M), reunion(vars(M'), vars(s)));
            var zf := addAnUniqueId(S)[0];
            assert !(zf in S);
            assert zf != a && zf != b;
            varsOfALambdaIncludesVarsofASubLambda(M);
            assert !(zf in vars(M)) && !(zf in vars(M')) && !(zf in vars(s));
            assert !(zf in vars(body));

            var body_alt := substitution(body, z, Var(zf));
            var s_alt := substitution(s, z, Var(zf));

            ParRedRename(body, s, z, zf);
            CaSubstIsNaiveWhenFresh(body, z, zf);
            CaSubstIsNaiveWhenFresh(s, z, zf);
            assert parallelReduction(body_alt, s_alt);

            subsitutionOfVarDoesNotChangeHeightFORVARIABLES(body, z, Var(zf));
            ParRedRename(body_alt, s_alt, a, b);
            var PbA := caSubstitution(body_alt, a, Var(b));
            var rr := caSubstitution(s_alt, a, Var(b));
            assert parallelReduction(PbA, rr);

            SubstAlphaEquivalence(body, z, zf);
            EqualTermsAreAlphaEquilvalent(Var(b), Var(b));
            CaSubstEquivalence(M, Var(b), Lambda(zf, body_alt), Var(b), a);
            SubstPushesIntoSafeLambda(zf, body_alt, a, Var(b));
            AlphaEquivTransitive(Mca, caSubstitution(Lambda(zf, body_alt), a, Var(b)), Lambda(zf, PbA));

            SubstAlphaEquivalence(s, z, zf);
            AlphaEquivTransitive(Lambda(zf, s_alt), Lambda(z, s), M');
            CaSubstEquivalence(Lambda(zf, s_alt), Var(b), M', Var(b), a);
            SubstPushesIntoSafeLambda(zf, s_alt, a, Var(b));
            AlphaEquivSymmetric(caSubstitution(Lambda(zf, s_alt), a, Var(b)), Lambda(zf, rr));
            AlphaEquivTransitive(Lambda(zf, rr), caSubstitution(Lambda(zf, s_alt), a, Var(b)), M'ca);

            ParRedLambdaIntro(zf, PbA, rr, M'ca);
            AlphaEquivSymmetric(Mca, Lambda(zf, PbA));
            EqualTermsAreAlphaEquilvalent(M'ca, M'ca);
            CaSubsitutionOfVarDoesNotChangeHeightFORVARIABLES(body_alt, a, Var(b));
            ParallelReductionAlphaInvariance(Lambda(zf, PbA), M'ca, Mca, M'ca);
        }
        case Application(P, Q) => {
            if M'.Application? && parallelReduction(P, M'.t1) && parallelReduction(Q, M'.t2) {
                var Pp := M'.t1;
                var Qp := M'.t2;
                SubstDistributesOverApp(P, Q, a, Var(b));
                SubstDistributesOverApp(Pp, Qp, a, Var(b));
                ParRedRename(P, Pp, a, b);
                ParRedRename(Q, Qp, a, b);
                var PA := caSubstitution(P, a, Var(b));
                var QA := caSubstitution(Q, a, Var(b));
                var PpA := caSubstitution(Pp, a, Var(b));
                var QpA := caSubstitution(Qp, a, Var(b));
                ParRedCongIntro(PA, QA, PpA, QpA);
                AlphaEquivSymmetric(Mca, Application(PA, QA));
                AlphaEquivSymmetric(M'ca, Application(PpA, QpA));
                CaSubsitutionOfVarDoesNotChangeHeightFORVARIABLES(P, a, Var(b));
                CaSubsitutionOfVarDoesNotChangeHeightFORVARIABLES(Q, a, Var(b));
                ParallelReductionAlphaInvariance(Application(PA, QA), Application(PpA, QpA), Mca, M'ca);
            } else {
                match P {
                    case Lambda(z, Pb) => {
                        var Pb', Q'' :| parallelReduction(Pb, Pb') && parallelReduction(Q, Q'')
                                        && alphaEquivalence(M', caSubstitution(Pb', z, Q''));
                        var S := addition(a, addition(b, reunion(vars(M), reunion(vars(M'),
                                    reunion(vars(Pb'), vars(Q''))))));
                        reunionIncludesBothSets(vars(Pb'), vars(Q''));
                        reunionIncludesBothSets(vars(M'), reunion(vars(Pb'), vars(Q'')));
                        reunionIncludesBothSets(vars(M), reunion(vars(M'), reunion(vars(Pb'), vars(Q''))));
                        var zf := addAnUniqueId(S)[0];
                        assert !(zf in S);
                        assert zf != a && zf != b;
                        varsOfALambdaIncludesVarsofASubLambda(M);
                        varsOfALambdaIncludesVarsofASubLambda(P);
                        assert !(zf in vars(M)) && !(zf in vars(M')) && !(zf in vars(Pb')) && !(zf in vars(Q''));
                        assert !(zf in vars(P));
                        assert !(zf in vars(Pb)) && !(zf in vars(Q));

                        var Pb_alt := substitution(Pb, z, Var(zf));
                        var Pb'_alt := substitution(Pb', z, Var(zf));

                        assert parallelReduction(Pb, Pb');
                        assert lHeight(Pb) < lHeight(M);
                        ParRedRename(Pb, Pb', z, zf);
                        CaSubstIsNaiveWhenFresh(Pb, z, zf);
                        CaSubstIsNaiveWhenFresh(Pb', z, zf);
                        assert parallelReduction(Pb_alt, Pb'_alt);

                        subsitutionOfVarDoesNotChangeHeightFORVARIABLES(Pb, z, Var(zf));
                        var PbA := caSubstitution(Pb_alt, a, Var(b));
                        var QA := caSubstitution(Q, a, Var(b));
                        var P2 := caSubstitution(Pb'_alt, a, Var(b));
                        var N2 := caSubstitution(Q'', a, Var(b));

                        ParRedRename(Pb_alt, Pb'_alt, a, b);
                        ParRedRename(Q, Q'', a, b);
                        assert parallelReduction(PbA, P2);
                        assert parallelReduction(QA, N2);

                        var LHSapp := Application(Lambda(zf, PbA), QA);

                        SubstAlphaEquivalence(Pb, z, zf);
                        EqualTermsAreAlphaEquilvalent(Q, Q);
                        ApplicationEquivalence(Lambda(z, Pb), Lambda(zf, Pb_alt), Q, Q);
                        EqualTermsAreAlphaEquilvalent(Var(b), Var(b));
                        CaSubstEquivalence(M, Var(b), Application(Lambda(zf, Pb_alt), Q), Var(b), a);
                        SubstDistributesOverApp(Lambda(zf, Pb_alt), Q, a, Var(b));
                        SubstPushesIntoSafeLambda(zf, Pb_alt, a, Var(b));
                        EqualTermsAreAlphaEquilvalent(QA, QA);
                        ApplicationEquivalence(caSubstitution(Lambda(zf, Pb_alt), a, Var(b)), Lambda(zf, PbA), QA, QA);
                        AlphaEquivTransitive(Mca,
                                             caSubstitution(Application(Lambda(zf, Pb_alt), Q), a, Var(b)),
                                             Application(caSubstitution(Lambda(zf, Pb_alt), a, Var(b)), QA));
                        AlphaEquivTransitive(Mca,
                                             Application(caSubstitution(Lambda(zf, Pb_alt), a, Var(b)), QA),
                                             LHSapp);

                        SubstAlphaEquivalence(Pb', z, zf);
                        SubstRespectsBinderAlpha(z, Pb', zf, Pb'_alt, Q'');
                        AlphaEquivTransitive(M', caSubstitution(Pb', z, Q''), caSubstitution(Pb'_alt, zf, Q''));
                        EqualTermsAreAlphaEquilvalent(Var(b), Var(b));
                        CaSubstEquivalence(M', Var(b), caSubstitution(Pb'_alt, zf, Q''), Var(b), a);
                        SubstitutionLemma(Pb'_alt, Q'', Var(b), zf, a);
                        AlphaEquivTransitive(M'ca,
                                             caSubstitution(caSubstitution(Pb'_alt, zf, Q''), a, Var(b)),
                                             caSubstitution(P2, zf, N2));

                        ParRedBetaIntro(zf, PbA, QA, P2, N2, M'ca);
                        AlphaEquivSymmetric(Mca, LHSapp);
                        EqualTermsAreAlphaEquilvalent(M'ca, M'ca);
                        CaSubsitutionOfVarDoesNotChangeHeightFORVARIABLES(Pb_alt, a, Var(b));
                        CaSubsitutionOfVarDoesNotChangeHeightFORVARIABLES(Q, a, Var(b));
                        ParallelReductionAlphaInvariance(LHSapp, M'ca, Mca, M'ca);
                    }
                    case _ => { assert false; }
                }
            }
        }
    }
}

lemma {:vcs_split_on_every_assert} ParRedAlphaUnderBinder(x:Id, B:LambdaTerm, R:LambdaTerm, x2:Id, B2arg:LambdaTerm)
    requires parallelReduction(B, R)
    requires alphaEquivalence(Lambda(x, B), Lambda(x2, B2arg))
    ensures exists RR :: parallelReduction(B2arg, RR) && alphaEquivalence(Lambda(x2, RR), Lambda(x, R))
    decreases lHeight(B), 2
{
    if x == x2 {
        StripSameBinder(x, B, B2arg);
        EqualTermsAreAlphaEquilvalent(R, R);
        ParallelReductionAlphaInvariance(B, R, B2arg, R);
        EqualTermsAreAlphaEquilvalent(Lambda(x2, R), Lambda(x, R));
        assert parallelReduction(B2arg, R) && alphaEquivalence(Lambda(x2, R), Lambda(x, R));
    } else {
        BinderRenameNotFree(x, B, x2, B2arg);
        ParRedPreservesNonFree(B, R, x2);
        AvoidVarInTerm(B, x2);
        var Bc :| alphaEquivalence(B, Bc) && !(x2 in vars(Bc));
        AvoidVarInTerm(R, x2);
        var Rc :| alphaEquivalence(R, Rc) && !(x2 in vars(Rc));

        AlphaSameHeight(B, Bc);
        ParallelReductionAlphaInvariance(B, R, Bc, Rc);

        AlphaEquivSymmetric(B, Bc);
        AlphaCongruenceLambda(x, Bc, B);
        AlphaEquivTransitive(Lambda(x, Bc), Lambda(x, B), Lambda(x2, B2arg));

        ParRedRename(Bc, Rc, x, x2);
        var BcS := caSubstitution(Bc, x, Var(x2));
        var RR := caSubstitution(Rc, x, Var(x2));
        assert parallelReduction(BcS, RR);

        CaSubstIsNaiveWhenFresh(Bc, x, x2);
        SubstAlphaEquivalence(Bc, x, x2);
        AlphaEquivSymmetric(Lambda(x, Bc), Lambda(x2, B2arg));
        AlphaEquivTransitive(Lambda(x2, B2arg), Lambda(x, Bc), Lambda(x2, BcS));
        StripSameBinder(x2, B2arg, BcS);
        AlphaEquivSymmetric(B2arg, BcS);

        CaSubsitutionOfVarDoesNotChangeHeightFORVARIABLES(Bc, x, Var(x2));
        EqualTermsAreAlphaEquilvalent(RR, RR);
        ParallelReductionAlphaInvariance(BcS, RR, B2arg, RR);

        CaSubstIsNaiveWhenFresh(Rc, x, x2);
        SubstAlphaEquivalence(Rc, x, x2);
        AlphaEquivSymmetric(R, Rc);
        AlphaCongruenceLambda(x, Rc, R);
        AlphaEquivSymmetric(Lambda(x, Rc), Lambda(x2, RR));
        AlphaEquivTransitive(Lambda(x2, RR), Lambda(x, Rc), Lambda(x, R));

        assert parallelReduction(B2arg, RR) && alphaEquivalence(Lambda(x2, RR), Lambda(x, R));
    }
}

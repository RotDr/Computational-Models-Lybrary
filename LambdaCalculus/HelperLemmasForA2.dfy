include "ParallelReduction.dfy"
include "SubstitutionsAndSets.dfy"



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





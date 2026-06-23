include "AlphaEquivalence.dfy"
include "SubstitutionsAndSets.dfy"

lemma AlphaInsertUnused(r:LambdaTerm, r':LambdaTerm, P1:seq<Id>, P2:seq<Id>, W1:seq<Id>, W2:seq<Id>)
    requires |P1| == |P2| && |W1| == |W2|
    requires alphaEquivalence'(r, r', P1, P2)
    requires forall v :: v in vars(r)  ==> !(v in W1)
    requires forall v :: v in vars(r') ==> !(v in W2)
    ensures alphaEquivalence'(r, r', W1 + P1, W2 + P2)
    decreases r
{
    match r
        case Var(y) => {
            var y' :| r' == Var(y');

            findId_concat_notInLeft(W1, P1, y);
            findId_concat_notInLeft(W2, P2, y');
        }
        case Lambda(z, b) => {
            var z', b' :| r' == Lambda(z', b');

            varsOfALambdaIncludesVarsofASubLambda(r);
            varsOfALambdaIncludesVarsofASubLambda(r');

            assert forall v :: v in vars(b)  ==> !(v in W1);
            assert forall v :: v in vars(b') ==> !(v in W2);
            AlphaInsertUnused(b, b', P1 + [z], P2 + [z'], W1, W2);
            assert W1 + (P1 + [z]) == (W1 + P1) + [z];
            assert W2 + (P2 + [z']) == (W2 + P2) + [z'];
        }
        case Application(l, rr) => {
            var l', rr' :| r' == Application(l', rr');
            varsOfALambdaIncludesVarsofASubLambda(r);
            varsOfALambdaIncludesVarsofASubLambda(r');
            assert forall v :: v in vars(l)   ==> !(v in W1);
            assert forall v :: v in vars(rr)  ==> !(v in W1);
            assert forall v :: v in vars(l')  ==> !(v in W2);
            assert forall v :: v in vars(rr') ==> !(v in W2);
            AlphaInsertUnused(l,  l',  P1, P2, W1, W2);
            AlphaInsertUnused(rr, rr', P1, P2, W1, W2);
        }
}

lemma SubstNaiveRespectsAlpha'(A:LambdaTerm, A':LambdaTerm, x:Id, r:LambdaTerm, r':LambdaTerm,
                               id1:seq<Id>, id2:seq<Id>)
    requires |id1| == |id2|
    requires alphaEquivalence'(A, A', id1, id2)
    requires alphaEquivalence(r, r')
    requires !(x in id1) && !(x in id2)
    requires !(x in bound(A)) && !(x in bound(A'))
    requires forall w :: w in id1 ==> !(w in vars(r))
    requires forall w :: w in id2 ==> !(w in vars(r'))
    requires forall w :: w in bound(A)  ==> !(w in vars(r))
    requires forall w :: w in bound(A') ==> !(w in vars(r'))
    ensures alphaEquivalence'(substitution(A, x, r), substitution(A', x, r'), id1, id2)
    decreases A
{
    match A
        case Var(y) => {
            var y' :| A' == Var(y');
            if y == x {
                // y==x => (since x !in id1) y'==x ; both substitute to r / r'.
                assert substitution(A, x, r)  == r;
                assert substitution(A', x, r') == r';
                AlphaInsertUnused(r, r', [], [], id1, id2);
            } else {
                // y!=x => y'!=x ; both unchanged.
                assert substitution(A, x, r)  == Var(y);
                assert substitution(A', x, r') == Var(y');
            }
        }
        case Lambda(w, b) => {
            var w', b' :| A' == Lambda(w', b');
            // x !in bound(A) => w != x ; substitution recurses under the binder.
            assert substitution(A, x, r)   == Lambda(w,  substitution(b,  x, r));
            assert substitution(A', x, r')  == Lambda(w', substitution(b', x, r'));
            SubstNaiveRespectsAlpha'(b, b', x, r, r', id1 + [w], id2 + [w']);
        }
        case Application(l, rr) => {
            var l', rr' :| A' == Application(l', rr');
            SubstNaiveRespectsAlpha'(l,  l',  x, r, r', id1, id2);
            SubstNaiveRespectsAlpha'(rr, rr', x, r, r', id1, id2);
        }
}

lemma SubstNaiveRespectsAlpha(A:LambdaTerm, A':LambdaTerm, x:Id, r:LambdaTerm, r':LambdaTerm)
    requires alphaEquivalence(A, A')
    requires alphaEquivalence(r, r')
    requires !(x in bound(A)) && !(x in bound(A'))
    requires forall w :: w in bound(A)  ==> !(w in vars(r))
    requires forall w :: w in bound(A') ==> !(w in vars(r'))
    ensures alphaEquivalence(substitution(A, x, r), substitution(A', x, r'))
{
    SubstNaiveRespectsAlpha'(A, A', x, r, r', [], []);
}


lemma CaSubstIsNaiveNoCapture(t:LambdaTerm, x:Id, r:LambdaTerm, ids:seq<Id>)
    requires allUnique(ids)
    requires includes(ids, vars(t)) && includes(ids, vars(r)) && x in ids
    requires forall w :: w in bound(t) ==> !(w in free(r))
    ensures caSubstitution'(t, x, r, ids) == substitution(t, x, r)
    decreases lHeight(t)
{
    match t
        case Var(y) => { }
        case Lambda(y, b) => {
            if y == x {
            } else {
                // y is a binder of t, hence y !in free(r): the non-capture branch is taken.
                assert y in bound(t);
                assert !(y in free(r));
                varsOfALambdaIncludesVarsofASubLambda(t);
                CaSubstIsNaiveNoCapture(b, x, r, ids);
            }
        }
        case Application(l, rr) => {
            varsOfALambdaIncludesVarsofASubLambda(t);
            CaSubstIsNaiveNoCapture(l,  x, r, ids);
            CaSubstIsNaiveNoCapture(rr, x, r, ids);
        }
}


lemma NotInVarsSubst(M:LambdaTerm, x:Id, r:LambdaTerm, Z:Id)
    requires !(Z in vars(M)) && !(Z in vars(r))
    ensures !(Z in vars(substitution(M, x, r)))
    decreases M
{
    match M
        case Var(v) => { }
        case Lambda(v, c) => {
            if v == x {
            } else {
                varsOfALambdaIncludesVarsofASubLambda(M);
                NotInVarsSubst(c, x, r, Z);
            }
        }
        case Application(l, rr) => {
            varsOfALambdaIncludesVarsofASubLambda(M);
            NotInVarsSubst(l, x, r, Z);
            NotInVarsSubst(rr, x, r, Z);
        }
}


lemma SubstSwap(M:LambdaTerm, y:Id, Z:Id, x:Id, r:LambdaTerm)
    requires x != y
    requires !(y in free(r))
    requires Z != x
    requires !(Z in vars(M))
    requires forall w :: w in bound(M) ==> !(w in free(r))
    ensures substitution(substitution(M, y, Var(Z)), x, r)
         == substitution(substitution(M, x, r), y, Var(Z))
    decreases M
{
    match M
        case Var(v) => {
            if v == x {
                SubstNoFree(r, y, Var(Z));
            }
        }
        case Lambda(v, c) => {
            if v == x {
            } else if v == y {
            } else {
                varsOfALambdaIncludesVarsofASubLambda(M);
                SubstSwap(c, y, Z, x, r);
            }
        }
        case Application(l, rr) => {
            varsOfALambdaIncludesVarsofASubLambda(M);
            SubstSwap(l,  y, Z, x, r);
            SubstSwap(rr, y, Z, x, r);
        }
}


lemma FreeInVars(t:LambdaTerm)
    ensures forall w :: w in free(t) ==> w in vars(t)
    decreases t
{
    match t
        case Var(_) => { }
        case Lambda(y, b) => {
            FreeInVars(b);
            varsOfALambdaIncludesVarsofASubLambda(t);
        }
        case Application(l, r) => {
            FreeInVars(l);
            FreeInVars(r);
            varsOfALambdaIncludesVarsofASubLambda(t);
        }
}

lemma FreeVarSubst(M:LambdaTerm, v:Id, Z:Id)
    requires Z != v
    requires !(Z in vars(M))
    ensures   (v in free(M)) ==> free(substitution(M, v, Var(Z))) == free(M) - {v} + {Z}
    ensures !(v in free(M)) ==> free(substitution(M, v, Var(Z))) == free(M)
    decreases M
{
    match M
        case Var(u) => { }
        case Lambda(w, c) => {
            if w == v {
            } else {
                varsOfALambdaIncludesVarsofASubLambda(M);
                FreeVarSubst(c, v, Z);
            }
        }
        case Application(l, r) => {
            varsOfALambdaIncludesVarsofASubLambda(M);
            FreeVarSubst(l, v, Z);
            FreeVarSubst(r, v, Z);
        }
}


lemma {:vcs_split_on_every_assert} FreshenExists(s:LambdaTerm, avoid:seq<Id>)
    requires allUnique(avoid)
    ensures exists sf:LambdaTerm ::
        alphaEquivalence(s, sf)
        && (forall w :: w in bound(sf) ==> !(w in avoid))
        && free(sf) == free(s)
    decreases s
{
    match s
        case Var(u) => {
            EqualTermsAreAlphaEquilvalent(s, s);
            assert alphaEquivalence(s, s) && (forall w :: w in bound(s) ==> !(w in avoid)) && free(s) == free(s);
        }
        case Application(l, rr) => {
            FreshenExists(l, avoid);
            var lf :| alphaEquivalence(l, lf) && (forall w :: w in bound(lf) ==> !(w in avoid)) && free(lf) == free(l);
            FreshenExists(rr, avoid);
            var rrf :| alphaEquivalence(rr, rrf) && (forall w :: w in bound(rrf) ==> !(w in avoid)) && free(rrf) == free(rr);
            var sf := Application(lf, rrf);
            ApplicationEquivalence(l, lf, rr, rrf);
            assert free(sf) == free(s);
            assert alphaEquivalence(s, sf) && (forall w :: w in bound(sf) ==> !(w in avoid)) && free(sf) == free(s);
        }
        case Lambda(v, c) => {
            FreshenExists(c, avoid);
            var cf :| alphaEquivalence(c, cf) && (forall w :: w in bound(cf) ==> !(w in avoid)) && free(cf) == free(c);
            // fresh Z avoiding `avoid`, vars(cf), and vars(s) (so Z != v).
            var combined := reunion(reunion(avoid, vars(cf)), vars(s));
            reunionIsGoodForWork(reunion(avoid, vars(cf)), vars(s));
            reunionIsGoodForWork(avoid, vars(cf));
            reunionIncludesBothSets(reunion(avoid, vars(cf)), vars(s));
            reunionIncludesBothSets(avoid, vars(cf));
            var Z := addAnUniqueId(combined)[0];
            assert !(Z in combined);
            assert !(Z in avoid) && !(Z in vars(cf)) && !(Z in vars(s));
            assert Z != v;     // v in vars(s)
            varsOfALambdaIncludesVarsofASubLambda(s);   // v in vars(s)
            var sf := Lambda(Z, substitution(cf, v, Var(Z)));
            // alpha(s, sf)
            AlphaCongruenceLambda(v, c, cf);
            SubstAlphaEquivalence(cf, v, Z);
            AlphaEquivTransitive(Lambda(v, c), Lambda(v, cf), Lambda(Z, substitution(cf, v, Var(Z))));
            // bound(sf)
            BoundSubstVar(cf, v, Z);
            // free(sf): split on whether v is free in cf, with Z !in free(cf).
            FreeInVars(cf);
            assert !(Z in free(cf));
            FreeVarSubst(cf, v, Z);
            assert free(sf) == free(substitution(cf, v, Var(Z))) - {Z};
            if v in free(cf) {
                assert free(substitution(cf, v, Var(Z))) == free(cf) - {v} + {Z};
                assert free(sf) == free(cf) - {v};
            } else {
                assert free(substitution(cf, v, Var(Z))) == free(cf);
                assert free(sf) == free(cf);
                assert free(sf) == free(cf) - {v};
            }
            assert free(cf) == free(c);
            assert free(s) == free(c) - {v};
            assert free(sf) == free(s);
            assert alphaEquivalence(s, sf) && (forall w :: w in bound(sf) ==> !(w in avoid)) && free(sf) == free(s);
        }
}


lemma CaSubstLambdaUnfoldNoCapture(y:Id, b:LambdaTerm, x:Id, r:LambdaTerm, ids:seq<Id>)
    requires allUnique(ids)
    requires includes(ids, vars(Lambda(y, b))) && includes(ids, vars(r)) && x in ids
    requires y != x
    requires !(y in free(r))
    ensures caSubstitution'(Lambda(y, b), x, r, ids) == Lambda(y, caSubstitution'(b, x, r, ids))
{
    varsOfALambdaIncludesVarsofASubLambda(Lambda(y, b));
}


lemma SubstTfUnfold(bf:LambdaTerm, y:Id, Z:Id, x:Id, r:LambdaTerm)
    requires x != y
    requires !(y in free(r))
    requires Z != x
    requires !(Z in vars(bf))
    requires forall w :: w in bound(bf) ==> !(w in free(r))
    ensures substitution(Lambda(Z, substitution(bf, y, Var(Z))), x, r)
         == Lambda(Z, substitution(substitution(bf, x, r), y, Var(Z)))
{
    SubstSwap(bf, y, Z, x, r);
}


lemma {:vcs_split_on_every_assert} BridgeExists(t:LambdaTerm, x:Id, r:LambdaTerm, ids:seq<Id>)
    requires allUnique(ids)
    requires includes(ids, vars(t)) && includes(ids, vars(r)) && x in ids
    ensures exists tf:LambdaTerm ::
        alphaEquivalence(t, tf)
        && (forall w :: w in bound(tf) ==> !(w in vars(r)))
        && !(x in bound(tf))
        && alphaEquivalence(caSubstitution'(t, x, r, ids), substitution(tf, x, r))
    decreases lHeight(t)
{
    match t
        case Var(y) => {
            var tf := Var(y);
            EqualTermsAreAlphaEquilvalent(t, tf);
            EqualTermsAreAlphaEquilvalent(caSubstitution'(t, x, r, ids), substitution(tf, x, r));
            assert alphaEquivalence(t, tf)
                && (forall w :: w in bound(tf) ==> !(w in vars(r)))
                && !(x in bound(tf))
                && alphaEquivalence(caSubstitution'(t, x, r, ids), substitution(tf, x, r));
        }
        case Application(l, rr) => {
            varsOfALambdaIncludesVarsofASubLambda(t);
            BridgeExists(l, x, r, ids);
            var lf :| alphaEquivalence(l, lf) && (forall w :: w in bound(lf) ==> !(w in vars(r)))
                      && !(x in bound(lf)) && alphaEquivalence(caSubstitution'(l, x, r, ids), substitution(lf, x, r));
            BridgeExists(rr, x, r, ids);
            var rrf :| alphaEquivalence(rr, rrf) && (forall w :: w in bound(rrf) ==> !(w in vars(r)))
                       && !(x in bound(rrf)) && alphaEquivalence(caSubstitution'(rr, x, r, ids), substitution(rrf, x, r));
            var tf := Application(lf, rrf);
            ApplicationEquivalence(l, lf, rr, rrf);
            ApplicationEquivalence(caSubstitution'(l, x, r, ids), substitution(lf, x, r),
                                   caSubstitution'(rr, x, r, ids), substitution(rrf, x, r));
            assert caSubstitution'(t, x, r, ids)
                == Application(caSubstitution'(l, x, r, ids), caSubstitution'(rr, x, r, ids));
            assert substitution(tf, x, r) == Application(substitution(lf, x, r), substitution(rrf, x, r));
            assert alphaEquivalence(t, tf)
                && (forall w :: w in bound(tf) ==> !(w in vars(r)))
                && !(x in bound(tf))
                && alphaEquivalence(caSubstitution'(t, x, r, ids), substitution(tf, x, r));
        }
        case Lambda(y, b) => {
            varsOfALambdaIncludesVarsofASubLambda(t);    
            if y == x {
                var avoidSeq := addition(x, vars(r));
                FreshenExists(t, avoidSeq);
                var tf :| alphaEquivalence(t, tf) && (forall w :: w in bound(tf) ==> !(w in avoidSeq)) && free(tf) == free(t);
                assert !(x in free(t));            // t = λx.b
                assert !(x in free(tf));
                SubstNoFree(tf, x, r);             // substitution(tf,x,r) == tf
                assert caSubstitution'(t, x, r, ids) == t;
                assert x in avoidSeq;
                assert forall w :: w in vars(r) ==> w in avoidSeq;
                assert alphaEquivalence(t, tf)
                    && (forall w :: w in bound(tf) ==> !(w in vars(r)))
                    && !(x in bound(tf))
                    && alphaEquivalence(caSubstitution'(t, x, r, ids), substitution(tf, x, r));
            } else if !(y in free(r)) {

                BridgeExists(b, x, r, ids);
                var bf :| alphaEquivalence(b, bf) && (forall w :: w in bound(bf) ==> !(w in vars(r)))
                          && !(x in bound(bf)) && alphaEquivalence(caSubstitution'(b, x, r, ids), substitution(bf, x, r));
                var pool := addition(x, reunion(vars(r), reunion(vars(bf), vars(b))));
                reunionIsGoodForWork(vars(bf), vars(b));
                reunionIsGoodForWork(vars(r), reunion(vars(bf), vars(b)));
                reunionIncludesBothSets(vars(r), reunion(vars(bf), vars(b)));
                reunionIncludesBothSets(vars(bf), vars(b));
                var Z := addAnUniqueId(pool)[0];
                assert !(Z in pool);
                assert Z != x && !(Z in vars(r)) && !(Z in vars(bf)) && !(Z in vars(b));
                var tf := Lambda(Z, substitution(bf, y, Var(Z)));

                AlphaCongruenceLambda(y, b, bf);
                SubstAlphaEquivalence(bf, y, Z);
                AlphaEquivTransitive(Lambda(y, b), Lambda(y, bf), tf);

                CaSubstLambdaUnfoldNoCapture(y, b, x, r, ids);
                AlphaCongruenceLambda(y, caSubstitution'(b, x, r, ids), substitution(bf, x, r));
                FreeInVars(r);
                SubstTfUnfold(bf, y, Z, x, r);
                NotInVarsSubst(bf, x, r, Z);
                SubstAlphaEquivalence(substitution(bf, x, r), y, Z);
                assert substitution(tf, x, r) == Lambda(Z, substitution(substitution(bf, x, r), y, Var(Z)));
                AlphaEquivTransitive(Lambda(y, caSubstitution'(b, x, r, ids)),
                                     Lambda(y, substitution(bf, x, r)),
                                     substitution(tf, x, r));
                BoundSubstVar(bf, y, Z);
                assert alphaEquivalence(t, tf)
                    && (forall w :: w in bound(tf) ==> !(w in vars(r)))
                    && !(x in bound(tf))
                    && alphaEquivalence(caSubstitution'(t, x, r, ids), substitution(tf, x, r));
            } else {

                var ids0 := addAnUniqueId(ids);
                var z0 := ids0[0];
                var u0 := substitution(b, y, Var(z0));
                subsitutionOfVarDoesNotChangeHeightFORVARIABLES(b, y, Var(z0));
                newIdsDueToSubstitution(b, y, Var(z0), ids0);
                BridgeExists(u0, x, r, ids0);
                var u0f :| alphaEquivalence(u0, u0f) && (forall w :: w in bound(u0f) ==> !(w in vars(r)))
                           && !(x in bound(u0f)) && alphaEquivalence(caSubstitution'(u0, x, r, ids0), substitution(u0f, x, r));
                var tf := Lambda(z0, u0f);
                assert !(z0 in ids);                 
                assert !(z0 in vars(r)) && z0 != x;  
                assert !(z0 in vars(b));             

                SubstAlphaEquivalence(b, y, z0);
                AlphaCongruenceLambda(z0, u0, u0f);
                AlphaEquivTransitive(Lambda(y, b), Lambda(z0, u0), tf);

                assert caSubstitution'(t, x, r, ids) == Lambda(z0, caSubstitution'(u0, x, r, ids0));
                AlphaCongruenceLambda(z0, caSubstitution'(u0, x, r, ids0), substitution(u0f, x, r));
                assert substitution(tf, x, r) == Lambda(z0, substitution(u0f, x, r));
                assert alphaEquivalence(t, tf)
                    && (forall w :: w in bound(tf) ==> !(w in vars(r)))
                    && !(x in bound(tf))
                    && alphaEquivalence(caSubstitution'(t, x, r, ids), substitution(tf, x, r));
            }
        }
}


lemma CaSubstPrimeRespectsAlphaProved(t1:LambdaTerm, t2:LambdaTerm, t1':LambdaTerm, t2':LambdaTerm,
                                      x:Id, ids:seq<Id>, ids':seq<Id>)
    requires alphaEquivalence(t1, t1') && alphaEquivalence(t2, t2')
    requires allUnique(ids) && allUnique(ids')
    requires includes(ids, vars(t1)) && includes(ids, vars(t2)) && x in ids
    requires includes(ids', vars(t1')) && includes(ids', vars(t2')) && x in ids'
    ensures alphaEquivalence(caSubstitution'(t1, x, t2, ids), caSubstitution'(t1', x, t2', ids'))
{
    BridgeExists(t1, x, t2, ids);
    var tf1 :| alphaEquivalence(t1, tf1) && (forall w :: w in bound(tf1) ==> !(w in vars(t2)))
               && !(x in bound(tf1)) && alphaEquivalence(caSubstitution'(t1, x, t2, ids), substitution(tf1, x, t2));
    BridgeExists(t1', x, t2', ids');
    var tf1' :| alphaEquivalence(t1', tf1') && (forall w :: w in bound(tf1') ==> !(w in vars(t2')))
                && !(x in bound(tf1')) && alphaEquivalence(caSubstitution'(t1', x, t2', ids'), substitution(tf1', x, t2'));
    AlphaEquivSymmetric(t1, tf1);
    AlphaEquivTransitive(tf1, t1, t1');
    AlphaEquivTransitive(tf1, t1', tf1');
    SubstNaiveRespectsAlpha(tf1, tf1', x, t2, t2');
    AlphaEquivSymmetric(caSubstitution'(t1', x, t2', ids'), substitution(tf1', x, t2'));
    AlphaEquivTransitive(caSubstitution'(t1, x, t2, ids), substitution(tf1, x, t2), substitution(tf1', x, t2'));
    AlphaEquivTransitive(caSubstitution'(t1, x, t2, ids), substitution(tf1', x, t2'), caSubstitution'(t1', x, t2', ids'));
}

lemma CaSubstPrimeRespectsAlpha(t1:LambdaTerm, t2:LambdaTerm, t1':LambdaTerm, t2':LambdaTerm, x:Id, ids:seq<Id>, ids':seq<Id>)
    requires alphaEquivalence(t1, t1') && alphaEquivalence(t2, t2')
    requires allUnique(ids) && allUnique(ids')
    requires includes(ids, vars(t1)) && includes(ids, vars(t2)) && x in ids
    requires includes(ids', vars(t1')) && includes(ids', vars(t2')) && x in ids'
    ensures alphaEquivalence(caSubstitution'(t1, x, t2, ids), caSubstitution'(t1', x, t2', ids'))
{
    CaSubstPrimeRespectsAlphaProved(t1, t2, t1', t2', x, ids, ids');
}


lemma AddingBanListIsAllowed(t1:LambdaTerm, x:Id, t2:LambdaTerm, ids:seq<Id>, ids2:seq<Id>)
    requires allUnique(ids) && allUnique(ids2)
    requires var s1:=vars(t1); allUnique(s1) && includes(ids, s1)
    requires var s2:=vars(t2); allUnique(s2) && includes(ids, s2)
    requires x in ids
    ensures var ids' := reunion(ids, ids2);
        allUnique(ids') &&
        includes(ids', vars(t1)) && includes(ids',vars(t2)) && 
        alphaEquivalence(caSubstitution'(t1, x, t2, ids), caSubstitution'(t1, x, t2, ids'))
    decreases lHeight(t1)
{
    var ids' := reunion(ids, ids2);
    
    reunionIsGoodForWork(ids, ids2); 
    reunionIncludesBothSets(ids, ids2); 
    
    forall id2:nat | id2 < |vars(t1)| ensures exists id1:nat :: id1 < |ids'| && ids'[id1] == vars(t1)[id2] {
        assert vars(t1)[id2] in ids; assert vars(t1)[id2] in ids';
    }
    forall id2:nat | id2 < |vars(t2)| ensures exists id1:nat :: id1 < |ids'| && ids'[id1] == vars(t2)[id2] {
        assert vars(t2)[id2] in ids; assert vars(t2)[id2] in ids';
    }

    match t1 {
        case Var(y) => {
            var sub1 := caSubstitution'(t1, x, t2, ids);
            var sub2 := caSubstitution'(t1, x, t2, ids');
            assert sub1 == sub2;
            EqualTermsAreAlphaEquilvalent(sub1, sub2);
        }
        case Application(a, b) => {
            varsOfALambdaIncludesVarsofASubLambda(t1);
            AddingBanListIsAllowed(a, x, t2, ids, ids2);
            AddingBanListIsAllowed(b, x, t2, ids, ids2);
            
            var sub1a := caSubstitution'(a, x, t2, ids);
            var sub1b := caSubstitution'(b, x, t2, ids);
            var sub2a := caSubstitution'(a, x, t2, ids');
            var sub2b := caSubstitution'(b, x, t2, ids');
            
            ApplicationEquivalence(sub1a, sub2a, sub1b, sub2b);
        }
        case Lambda(y, b) => {
            if y == x {
                var sub1 := caSubstitution'(t1, x, t2, ids);
                var sub2 := caSubstitution'(t1, x, t2, ids');
                assert sub1 == t1 && sub2 == t1;
                EqualTermsAreAlphaEquilvalent(sub1, sub2);
            } 
            else if !(y in free(t2)) {
                varsOfALambdaIncludesVarsofASubLambda(t1);
                AddingBanListIsAllowed(b, x, t2, ids, ids2);
                
                var sub1_body := caSubstitution'(b, x, t2, ids);
                var sub2_body := caSubstitution'(b, x, t2, ids');
                AlphaCongruenceLambda(y, sub1_body, sub2_body);
            } 
            else {

                var sub1 := caSubstitution'(t1, x, t2, ids);
                var sub2 := caSubstitution'(t1, x, t2, ids');
                EqualTermsAreAlphaEquilvalent(t1, t1);
                EqualTermsAreAlphaEquilvalent(t2, t2);
                assert x in ids';
                CaSubstPrimeRespectsAlpha(t1, t2, t1, t2, x, ids, ids');
            }
        }
    }
}

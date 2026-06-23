include "AlphaEquivalence.dfy"

lemma BoundSubstVar(M:LambdaTerm, y:Id, Z:Id)
    ensures bound(substitution(M, y, Var(Z))) == bound(M)
    decreases M
{
    match M
        case Var(_) => { }
        case Lambda(v, c) => {
            if v == y {
            } else {
                BoundSubstVar(c, y, Z);
            }
        }
        case Application(l, r) => {
            BoundSubstVar(l, y, Z);
            BoundSubstVar(r, y, Z);
        }
}

lemma SubstNoFree(t:LambdaTerm, a:Id, s:LambdaTerm)
    requires !(a in free(t))
    ensures substitution(t, a, s) == t
    decreases lHeight(t)
{
    match t
        case Var(y) => { }
        case Lambda(y, b) => {
            if y == a {
            } else {
                SubstNoFree(b, a, s);
            }
        }
        case Application(l, r) => {
            SubstNoFree(l, a, s);
            SubstNoFree(r, a, s);
        }
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


lemma NoFreeVariablesToReplace (M:LambdaTerm,x:Id,P:LambdaTerm)
    requires !(x in free(M))
    ensures alphaEquivalence(caSubstitution(M,x,P),M) 
{
    var ids:=reunion(vars(M),vars(P));
    reunionIncludesBothSets(vars(M),vars(P));
    var safe_ids:=addition(x,ids);
    NoFreeVariablesToReplace'(M,x,P,caSubstitution(M,x,P),safe_ids);
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



lemma sameFreeForEquivalent(t1:LambdaTerm,t2:LambdaTerm,x:Id)
    requires x in free(t1)
    requires alphaEquivalence(t1,t2)
    ensures x in free(t2)
{
    sameFreeForEquivalent'(t1,t2,x,[],[]);
}

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
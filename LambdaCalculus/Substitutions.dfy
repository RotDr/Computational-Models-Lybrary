include "./../objects.dfy"
include "FreeBoundAndVars.dfy"


function substitution(t:LambdaTerm,x:Id,t':LambdaTerm):LambdaTerm

{
    match t
        case Var(y) =>  if y==x 
                            then 
                            t' 
                        else Var(y)
        case Lambda(y,t1) =>    if y==x 
                                    then 
                                    
                                    t 
                                else   Lambda(y,substitution(t1,x,t'))
        case Application(t1,t2) => Application(substitution(t1,x,t'),substitution(t2,x,t'))
}

function caSubstitution(t:LambdaTerm,x:Id,t':LambdaTerm):LambdaTerm
{
    var ids:=reunion(vars(t),vars(t'));
    reunionIncludesBothSets(vars(t),vars(t'));
    var safe_ids := addition(x, ids);
    caSubstitution'(t,x,t',safe_ids)
}


lemma subsitutionOfVarDoesNotChangeHeightFORVARIABLES(t1:LambdaTerm,x:Id,t2:LambdaTerm)
    requires match t2 
                case Var(x) => true 
                case _ => false 
    ensures lHeight(substitution(t1,x,t2))==lHeight(t1)
{
    var t':=substitution(t1,x,t2);
    match t1{
        case Var(y) => {
            assert lHeight(t')==lHeight(t1);
            } 
        case Lambda(y,t) => {if (y==x) {
            assert t'==t1;
    } else {
        subsitutionOfVarDoesNotChangeHeightFORVARIABLES(t,x,t2);

    }
    }
        case Application(t1,t2) => {

        }
    }
}
            
lemma newIdsDueToSubstitution(t1:LambdaTerm,x:Id,t2:LambdaTerm,ids:seq<Id>)
    requires includes(ids,vars(t1))
    requires includes(ids,vars(t2))
    ensures includes(ids,vars(substitution(t1,x,t2)))
{
    match t1
        case Var(y) => {

        }
        case Lambda(y, t) => {
            if y == x {
            } else {
                var t' := substitution(t, x, t2);

                forall id2:nat | id2 < |vars(t)| 
                    ensures vars(t)[id2] in ids 
                {
                    assert vars(t)[id2] in vars(t1); 
                }

                assert includes(ids, vars(t));

                newIdsDueToSubstitution(t, x, t2, ids);

                var new_vars := addition(y, vars(t'));
                forall id2:nat | id2 < |new_vars|
                    ensures new_vars[id2] in ids 
                {
                    var elem := new_vars[id2];
                    if elem == y {
                        assert y in vars(t1); 
                    } else {
                        assert elem in vars(t'); 
                    }
                }
            }
        }
        case Application(t1', t2') => {
            var sub_t1' := substitution(t1', x, t2);
            var sub_t2' := substitution(t2', x, t2);

            forall id2:nat | id2 < |vars(t1')| ensures vars(t1')[id2] in ids {
                assert vars(t1')[id2] in vars(t1);
            }
            assert includes(ids, vars(t1'));

            forall id2:nat | id2 < |vars(t2')| ensures vars(t2')[id2] in ids {
                assert vars(t2')[id2] in vars(t1);
            }
            assert includes(ids, vars(t2'));

            newIdsDueToSubstitution(t1', x, t2, ids);
            newIdsDueToSubstitution(t2', x, t2, ids);

            var new_vars := reunion(vars(sub_t1'), vars(sub_t2'));
            forall id2:nat | id2 < |new_vars|
                ensures new_vars[id2] in ids
            {
                var elem := new_vars[id2];
                assert elem in vars(sub_t1') || elem in vars(sub_t2'); 
            }
        }
}

function caSubstitution'(t:LambdaTerm,x:Id,t':LambdaTerm,ids:seq<Id>):LambdaTerm
    requires allUnique(ids)
        requires var s1:=vars(t);
         allUnique(s1) && includes(ids,s1)
    requires var s2:=vars(t');
         allUnique(s2)  && includes(ids,s2)
    requires x in ids
    decreases lHeight(t)
{
    match t
        case Var(y) => if y==x then t' else Var(y)
        case Lambda(y,t1) => if y==x then t else
                                if !(y in free(t')) then Lambda(y,caSubstitution'(t1,x,t',ids))
                                    else
                                         var ids':=addAnUniqueId(ids);
                                            var vari:=Var(ids'[0]);
                                         var t2:=substitution(t1,y,vari);
                                         subsitutionOfVarDoesNotChangeHeightFORVARIABLES(t1,y,vari);
                                         varsOfALambdaIncludesVarsofASubLambda (t);
                                         newIdsDueToSubstitution(t1,y,vari,ids');
                                         Lambda(ids'[0],
                                         caSubstitution'(t2,x,t',ids'))
        case Application(t1,t2) => 
        varsOfALambdaIncludesVarsofASubLambda (t);
        Application(caSubstitution'(t1,x,t',ids),caSubstitution'(t2,x,t',ids))
}

lemma LambdaNullifiesSubstitution(t:LambdaTerm,x:Id,t':LambdaTerm)
    ensures caSubstitution(Lambda(x,t),x,t')==Lambda(x,t)
{
    var lt:=Lambda(x,t);
    var ids:=reunion(vars(lt),vars(t'));
    reunionIncludesBothSets(vars(lt),vars(t'));
    var safe_ids := addition(x, ids);
    var sub:=caSubstitution'(lt,x,t',safe_ids); 
    assert sub==caSubstitution(lt,x,t');
    match lt 
        case Lambda(y,t')=>
        {
            assert y==x;
            assert sub==lt;
        }
}

lemma CaSubstitution'OfVarDoesNotChangeHeight(t1:LambdaTerm, x:Id, t2:LambdaTerm, ids:seq<Id>)
    requires match t2 case Var(_) => true case _ => false
    requires allUnique(ids)
    requires includes(ids,vars(t1)) && includes(ids,vars(t2)) && x in ids
    ensures lHeight(caSubstitution'(t1, x, t2, ids)) == lHeight(t1)
    decreases lHeight(t1)
{
    match t1 {
        case Var(_) => {}
        case Lambda(y, t1') => {
            if y == x {
            } else if !(y in free(t2)) {
                CaSubstitution'OfVarDoesNotChangeHeight(t1', x, t2, ids);
            } else {
                var ids' := addAnUniqueId(ids);
                var vari  := Var(ids'[0]);
                var t2' := substitution(t1', y, vari);
                subsitutionOfVarDoesNotChangeHeightFORVARIABLES(t1', y, vari);
                 newIdsDueToSubstitution(t1',y,vari,ids');
                CaSubstitution'OfVarDoesNotChangeHeight(t2', x, t2, ids');
            }
        }
        case Application(t1', t1'') => {
            varsOfALambdaIncludesVarsofASubLambda (t1);
            CaSubstitution'OfVarDoesNotChangeHeight(t1', x, t2, ids);
            CaSubstitution'OfVarDoesNotChangeHeight(t1'', x, t2, ids);
        }
    }
}

lemma CaSubsitutionOfVarDoesNotChangeHeightFORVARIABLES(t1:LambdaTerm, x:Id, t2:LambdaTerm)
    requires match t2 case Var(_) => true case _ => false
    ensures lHeight(caSubstitution(t1, x, t2)) == lHeight(t1)
{
    var ids := reunion(vars(t1), vars(t2));
    reunionIncludesBothSets(vars(t1),vars(t2));
    var safe_ids:=addition(x,ids);
    CaSubstitution'OfVarDoesNotChangeHeight(t1, x, t2, safe_ids);
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
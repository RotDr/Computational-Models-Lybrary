include "objects.dfy"
type Id= nat
datatype LambdaTerm = Var(id:Id) | Lambda(x:Id,t:LambdaTerm) | Application( t1:LambdaTerm, t2:LambdaTerm)

function bound(t:LambdaTerm):set<Id>
{
        match t
                case Var(_) => {}
                case Lambda(x,t) => {x}+bound(t)
                case Application(t1,t2) => bound(t1)+bound(t2)
}
predicate includes(s1:seq<Id>,s2:seq<Id>)
    
{
    forall id2:nat::id2<|s2| ==> (exists id1:nat::id1<|s1| && s1[id1]==s2[id2])
}
function addition(x:Id,s:seq<Id>) : seq<Id>
    requires allUnique(s)
    ensures var s':=addition(x,s);
            allUnique(s') && x in s' && includes(s',s)

{
    if x in s 
        then s
    else  
        assert !(x in s);
        var s':=s+[x];
        assert x in s';
        assert allUnique(s');    
        assert forall id:nat::id<|s| ==> s[id]==s'[id];
        s'
}
function reunion(s1:seq<Id>,s2:seq<Id>) :seq<Id>
    requires allUnique(s1)
    requires allUnique(s2)
    ensures var s:=reunion(s1,s2);
        allUnique(s) 
        && (forall str:Id::str in s ==> (str in s1 || str in s2))
        && (forall str:Id::str in s1 || str in s2 ==> (str in s) )&&
        |s| >= |s1| && |s| >= |s2| 
{
    if s1==[] 
        then s2
    else
        [s1[0]]+reunion(remove(s1,s1[0]),remove(s2,s1[0]))
}
lemma reunionIncludesBothSets(s1:seq<Id>,s2:seq<Id>)
    requires allUnique(s1)
    requires allUnique(s2)
    ensures var s:=reunion(s1,s2);
    includes(s,s1) && includes(s,s2)
{
    var s:=reunion(s1,s2);
    assert forall str:Id :: str in s1 ==> str in s;
    assert forall str:Id :: str in s2 ==> str in s;

    forall id2:nat | id2 < |s1|
        ensures exists id1:nat :: id1 < |s| && s[id1] == s1[id2]
    {
        assert s1[id2] in s1;  
        assert s1[id2] in s;   
    }
    assert forall id2:nat::id2<|s1| ==> (exists id1:nat::id1<|s| && s[id1]==s1[id2]);
    forall id2:nat | id2 < |s2|
        ensures exists id1:nat :: id1 < |s| && s[id1] == s2[id2]
    {
        assert s2[id2] in s2;
        assert s2[id2] in s;
    }
    assert forall id2:nat::id2<|s2| ==> (exists id1:nat::id1<|s| && s[id1]==s2[id2]);
}
lemma elementNotInallUnique (s:seq<Id>,x:Id)
    requires !(x in s)
    requires allUnique(s)
    ensures allUnique([x]+s)
{
}    
ghost predicate allUnique (s:seq<Id>) 
{
    forall id1:nat,id2:nat::(id1<id2<|s|) ==> s[id1]!=s[id2]
}
predicate finds(s:seq<Id>,id:Id)
    ensures finds(s,id) <==> exists id1:nat::id1<|s| && s[id1]==id
{
    if s==[] then false 
        else 
            if s[0]==id then true 
                else finds(s[1..],id)

}

lemma reunionIsGoodForWork(s1:seq<Id>,s2:seq<Id>)
    requires allUnique(s1) 
    requires allUnique(s2) 
    ensures allUnique(reunion(s1,s2)) 
{
    var s:=reunion(s1,s2);
    assert forall str:Id::(str in s1 || str in s2) ==> (str in s);
    assert forall str:Id::str in s1 ==> (str in s);
    assert |s|>=|s1|;
    assert |s|>=|s1| && |s|>=|s2|;
}
function max(a:nat,b:nat) :nat 
    ensures var maxi:=max(a,b);
    maxi>=a && maxi>=b && (maxi==a || maxi==b)
{
    if a>b then a else b 
}

function highestId(s:seq<Id>) :nat
    ensures s!=[] ==> forall index:nat:: index<|s| ==> s[index]<=highestId(s)
    ensures s!=[] ==> exists index:nat:: index<|s| && s[index]==highestId(s)
    ensures s==[] ==> highestId(s)==0
    decreases s
{
        if s==[] then 0
        else
            max(s[0],highestId(s[1..]))
}
function addAnUniqueId(s:seq<Id>) :seq<Id>
    requires allUnique(s)
    ensures allUnique(addAnUniqueId(s))
    ensures includes(addAnUniqueId(s),s)
    ensures |addAnUniqueId(s)|==|s|+1
    ensures !(addAnUniqueId(s)[0] in s)
{
    if s==[] then 
        [0]
    else
        var s':= [highestId(s)+1]+s;
        assert forall id:nat::id<|s| ==> s[id]==s'[id+1];
        s'
}
function remove(s:seq<Id>,x:Id):seq<Id>
    requires allUnique(s) 
    ensures ! (x in remove(s,x))
    ensures allUnique(remove(s,x))
    ensures forall str:Id:: str in remove(s,x) ==> str in s
    ensures forall str:Id:: str in s && str!=x ==> str in remove(s,x)
    ensures |s|-1<=|remove(s,x)|<=|s|
    ensures includes(s,remove(s,x))
{
    if s==[] then []
    else 
        if   
            s[0]==x then s[1..]
        else 
        assert allUnique(remove(s[1..],x));
        assert ! (s[0] in remove(s[1..],x));
        elementNotInallUnique(remove(s[1..],x),s[0]);
        [s[0]]+remove(s[1..],x)

}

function free(t:LambdaTerm):set<Id>
{
     match t
                case Var(x) => {x}
                case Lambda(x,t) => free(t)-{x}
                case Application(t1,t2) => free(t1)+free(t2)
}

function freeVec(t:LambdaTerm):seq<Id>
    ensures forall id:nat:: (id in free(t)) ==> id in freeVec(t)
{
    match t
            case Var(x) => [x]
            case Lambda(x,t) => remove(freeVec(t),x)
            case Application(t1,t2) => reunion(freeVec(t1),freeVec(t2))
}

function vars(t:LambdaTerm):seq<Id>
    ensures allUnique(vars(t))
{
    match t
                case Var(x) => [x]
                case Lambda(x,t') => addition(x,vars(t'))
                case Application(t1,t2) => reunion(vars(t1),vars(t2))
}
lemma varsOfALambdaIncludesVarsofASubLambda (t:LambdaTerm)
    ensures var ids:=vars(t);
    
    match t
                case Var(x) => x in ids 
                case Lambda(x,t') => (x in ids) && includes(ids,vars(t'))
                case Application(t1,t2) => includes(ids,vars(t1)) && includes(ids,vars(t2))
{
    var ids:=vars(t);

    match t 
         case Var(x) => assert ids==[x];
                case Lambda(x,t') => assert ids==addition(x,vars(t'));
                case Application(t1,t2) => {
                    
                    assert ids==reunion(vars(t1),vars(t2));
                    reunionIncludesBothSets(vars(t1),vars(t2));
                    
                }
}
function lHeight(t:LambdaTerm):nat 
{
    match t
                case Var(x) => 1
                case Lambda(x,t') => 1+lHeight(t')
                case Application(t1,t2) => 1+max(lHeight(t1),lHeight(t2))
}
function substitution(t:LambdaTerm,x:Id,t':LambdaTerm):LambdaTerm
    decreases lHeight(t)
{
    match t
        case Var(y) =>  if y==x 
                            then 
                            assert vars(t)<=reunion(vars(t),vars(t'));
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
lemma CaSubstitutionRecursion (t:LambdaTerm,x:Id,t':LambdaTerm)
    ensures match t 
        case Lambda(y,t1) => (if y==x || !(y in free(t')) then caSubstitution(t,x,t')==Lambda(y,caSubstitution(t1,x,t')) else true)
        case Var(y) => true 
        case Application(t1,t2) => caSubstitution(t,x,t')==Application(caSubstitution(t1,x,t'),caSubstitution(t2,x,t'))
{
    
}

lemma CaSubstitutionRecursion' (t:LambdaTerm,x:Id,t':LambdaTerm,ids:seq<Id>)
    requires allUnique(ids)
    requires var s1:=vars(t);
         allUnique(s1) && includes(ids,s1)
    requires var s2:=vars(t');
         allUnique(s2)  && includes(ids,s2)
    requires x in ids
    ensures match t 
        case Lambda(y,t1) => (if y==x || !(y in free(t')) then caSubstitution(t,x,t')==Lambda(y,caSubstitution(t1,x,t')) else true)
        case Var(y) => true 
        case Application(t1,t2) => caSubstitution(t,x,t')==Application(caSubstitution(t1,x,t'),caSubstitution(t2,x,t'))
{
    
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

lemma ASubLambdaOfAUniqueLambdaIsUnique(t:LambdaTerm)
    requires allUnique(vars(t))
    ensures match t 
                case Var(_)=> true 
                case Application(t1,t2) => allUnique(vars(t1)) && allUnique(vars(t2))
                case Lambda(_,t') => allUnique(vars(t'))
{

}

function minim (a:nat,b:nat) : nat
    ensures minim(a,b)<=a && minim(a,b)<=b
    ensures minim(a,b)==a || minim(a,b)==b
{
    if a>b then b 
    else a 
}
predicate alphaEquivalence(t1:LambdaTerm,t2:LambdaTerm)

{
    alphaEquivalence'(t1,t2,[],[])
}
function findId(ids:seq<Id>,id:Id):Option<nat>
    ensures !(id in ids) <==> findId(ids,id)==None 
    ensures (id in ids) <==> findId(ids,id)!=None
    ensures (id in ids) <==> var pos:|findId(ids,id)==Some(pos);
    pos<|ids| && ids[pos]==id &&
    (forall pos2:nat:: pos<pos2<|ids| ==> ids[pos2]!=id)
    && 
    forall pos3:nat:: (pos3<|ids| && ids[pos3]==id ) ==> pos3<=pos

    decreases ids
{
    if ids==[] then None 
        else 
            var len:=|ids|;
            if ids[len-1]==id then 
                Some(len-1)
            else 
                findId(ids[..(len-1)],id)
}   
predicate alphaEquivalence'(t1:LambdaTerm,t2:LambdaTerm,id1:seq<Id>,id2:seq<Id>)
    decreases minim(lHeight(t1),lHeight(t2))

{
    
    match t1
        case Var(x) => (match t2 
                            case Var(y) => (
                                var r1:=findId(id1,x);
                                var r2:=findId(id2,y);
                                r1==r2 
                                &&
                                match r1
                                    case None => x==y
                                    case Some(_) => true 
                            )
                            case _ => false
                        ) 
        case Lambda(x,t1') => (match t2
                                case Lambda(y,t2') => 

                                    alphaEquivalence'(t1',t2',id1+[x],id2+[y])
                                case _=> false)
        case Application(t1',t1'') => match t2
                                        case Application(t2',t2'')=> alphaEquivalence'(t1',t2',id1,id2) && alphaEquivalence'(t1'',t2'',id1,id2)
                                        case _=>false
}

lemma EqualTermsAreAlphaEquilvalent(t1:LambdaTerm,t2:LambdaTerm)
    requires t1==t2 
    ensures alphaEquivalence(t1,t2)
{
    EqualTermsAreAlphaEquilvalent'(t1,t2,[],[]);
}

lemma EqualTermsAreAlphaEquilvalent'(t1:LambdaTerm,t2:LambdaTerm,id1:seq<Id>,id2:seq<Id>)
    requires forall y :: y in vars(t1) ==> findId(id1, y) == findId(id2, y)
    requires |id1|==|id2|
    requires t1==t2 
    ensures alphaEquivalence'(t1,t2,id1,id2)
    decreases minim(lHeight(t1),lHeight(t2))
{
        match t1
            case Var(x) => {
                assert t1==t2;
                var y:|t2==Var(y);
                assert x==y;
                var r1:=findId(id1,x);
                var r2:=findId(id2,y);
                assert r1==r2;
                if (r1==None)
                {
                    assert x==y;
                }
                assert alphaEquivalence'(t1,t2,id1,id2);
            }
            case Lambda(x,t1') => {
                var y,t2':|t2==Lambda(y,t2');
                assert y==x && t2'==t1';
                var id1':=id1+[x];
                var id2':=id2+[y];
                assert findId(id1',x)==Some(|id1'|-1);
                assert findId(id1',x)==findId(id2',y);
                EqualTermsAreAlphaEquilvalent'(t1',t2',id1+[x],id2+[y]);
            }
            case Application(t1',t1'') => {
                var t2',t2'':|t2==Application(t2',t2'');
                EqualTermsAreAlphaEquilvalent'(t1',t2',id1,id2);
                EqualTermsAreAlphaEquilvalent'(t1'',t2'',id1,id2);
            }
}


lemma SubstAlphaEquivalence (t:LambdaTerm,x:Id,x':Id)
    requires !(x' in vars(t))
    ensures alphaEquivalence(Lambda(x,t),Lambda(x',substitution(t,x,Var(x'))))
{
    assert []+[x]==[x] && []+[x']==[x'];
    SubstAlphaEquivalence'(t, x, x',substitution(t,x,Var(x')), [x], [x']);
}


lemma SubstAlphaEquivalence'(t:LambdaTerm, x:Id, x':Id,t2:LambdaTerm, id1:seq<Id>, id2:seq<Id>)
    requires |id1| == |id2| >0
    requires !(x' in vars(t))
    requires id1[0]==x && id2[0]==x'
    requires forall i :: 0 <= i < |id1| ==>
        (id1[i] == x <==> id2[i] == x') &&
        (id1[i] != x ==> id1[i] == id2[i])
    requires t2==substitution(t,x,Var(x'))
    ensures alphaEquivalence'(t, t2, id1, id2)
    decreases lHeight(t)
{
    match t 
        case Application(t1a,t1b) =>
        {
            var t2a:=substitution(t1a,x,Var(x'));
            var t2b:=substitution(t1b,x,Var(x'));
            assert t2==Application(t2a,t2b);

            SubstAlphaEquivalence'(t1a,x,x',t2a,id1,id2);
            SubstAlphaEquivalence'(t1b,x,x',t2b,id1,id2);

            assert alphaEquivalence'(t1a,t2a,id1,id2);
            assert alphaEquivalence'(t1b,t2b,id1,id2);

            assert alphaEquivalence'(t,t2,id1,id2);
        }
        case Lambda(z,t1') =>
        {
            if z==x
            {
                assert t2==t;
                var id1' := id1+[x] ;
                var id2' := id2+[x] ;
                

                forall y | y in vars(t1') ensures findId(id1', y) == findId(id2', y) {
                    if y != x {
                        assert y in vars(t);
                        assert y != x'; 
                    }
                }
                EqualTermsAreAlphaEquilvalent'(t1',t1',id1',id2');
                assert alphaEquivalence'(t, t2, id1, id2);
            }
            else 
            {
                
                var t2' := substitution(t1', x, Var(x'));
                assert t2 == Lambda(z, t2');

                var id1':=id1+[z];
                var id2':=id2+[z];

                SubstAlphaEquivalence'(t1',x,x',t2',id1',id2');

                assert alphaEquivalence'(t1',t2',id1',id2');
            }
        }
        case Var(z) =>
        {
            if (z==x)
            {
                assert t2==Var(x');
                var r1:=findId(id1,x);
                var r2:=findId(id2,x');
                assert r1!=None;
                
                assert r1==r2;
            }
            else 
            {
                assert t2==t;
                assert z!=x';
            }
        }
}

lemma AlphaEquivSymmetric(t1:LambdaTerm, t2:LambdaTerm)
    requires alphaEquivalence(t1, t2)
    ensures alphaEquivalence(t2, t1)
{
    AlphaEquivSymmetric'(t1,t2,[],[]);
}
lemma AlphaEquivSymmetric'(t1:LambdaTerm, t2:LambdaTerm,id1:seq<Id>,id2:seq<Id>)
    requires alphaEquivalence'(t1, t2,id1,id2)
    ensures alphaEquivalence'(t2, t1,id2,id1)
{


}

lemma ApplicationEquivalence(t1a:LambdaTerm,t2a:LambdaTerm,t1b:LambdaTerm,t2b:LambdaTerm)
    requires alphaEquivalence(t1a,t2a) && alphaEquivalence(t1b,t2b)
    ensures alphaEquivalence(Application(t1a,t1b),Application(t2a,t2b))
{

}

lemma AlphaEquivTransitive(t1:LambdaTerm, t2:LambdaTerm, t3:LambdaTerm)
    requires alphaEquivalence(t1, t2)
    requires alphaEquivalence(t2, t3)
    ensures alphaEquivalence(t1, t3)
{
    AlphaEquivTransitive'(t1,t2,t3,[],[],[]);
}
lemma AlphaEquivTransitive'(t1:LambdaTerm, t2:LambdaTerm, t3:LambdaTerm,id1:seq<Id>,id2:seq<Id>,id3:seq<Id>)
    requires alphaEquivalence'(t1, t2,id1,id2)
    requires alphaEquivalence'(t2, t3,id2,id3)
    ensures alphaEquivalence'(t1, t3,id1,id3)
{
    
}

lemma LambdaEquivalence(t1:LambdaTerm,t2:LambdaTerm,x1:Id,x2:Id)
    requires alphaEquivalence(t1,t2)
    requires !(x1 in free(t1)) && !(x2 in free(t2))
    ensures alphaEquivalence(Lambda(x1,t1),Lambda(x2,t2))
{
    LambdaEquivalence'(t1,t2,x1,x2,[],[]);
    assert [x1]==[x1]+[] && [x2]==[x2]+[];
    assert alphaEquivalence'(t1,t2,[x1],[x2]);
    assert [x1]==[]+[x1] && [x2]==[]+[x2];
}

lemma findId_prepend(ids: seq<Id>, x: Id, val: Id)
    ensures findId([val] + ids, x) ==
        match findId(ids, x) {
            case Some(i) => Some(i + 1)
            case None => if x == val then Some(0) else None
        }
{
    if ids == [] {
    } else {
        var len := |ids|;
        var prepended := [val] + ids;
        
        if ids[len-1] == x {
            assert prepended[|prepended|-1] == x;
        } else {
            assert prepended[..|prepended|-1] == [val] + ids[..len-1];
            findId_prepend(ids[..len-1], x, val);
        }
    }
}

lemma LambdaEquivalence'(t1:LambdaTerm,t2:LambdaTerm,x1:Id,x2:Id,id1:seq<Id>,id2:seq<Id>)
    requires alphaEquivalence'(t1,t2,id1,id2)
    requires x1 in free(t1) ==> x1 in id1  
    requires x2 in free(t2) ==> x2 in id2
    ensures alphaEquivalence'(t1,t2,[x1]+id1,[x2]+id2)
{
    match t1 
        case Var(x) =>
        {
            var y: Id :| t2 == Var(y);
            var r1 := findId(id1, x);
            var r2 := findId(id2, y);
            
            var id1' := [x1] + id1;
            var id2' := [x2] + id2;
            var r1' := findId(id1', x);
            var r2' := findId(id2', y);

            findId_prepend(id1, x, x1);
            findId_prepend(id2, y, x2);

            if r1 == None
            {
                assert x==y;
                
                assert x!=x1; 
                
                assert y!=x2;

                assert !(x in id1');
                assert !(y in id2');

                assert r1'==None;
                assert r2'==None;
            }
            else 
            {
                var i1 :|r1==Some(i1);
                assert r2==Some(i1); 

                var new_pos:=i1+1;

                assert id1'[new_pos]==x;
                
             

                
                assert r1'==Some(new_pos);

                assert id2'[new_pos]==y;

                assert r2' == Some(new_pos);
    }
        }
        case Lambda(x,t1')=>
        {
            var y:nat,t2':LambdaTerm:|t2==Lambda(y,t2');
            var id1':=id1+[x];
            var id2':=id2+[y];
            LambdaEquivalence'(t1',t2',x1,x2,id1',id2');
            assert [x1]+id1+[x]==[x1]+id1';
            assert [x2]+id2+[y]==[x2]+id2';

        }
        case Application(t1a,t1b)=>
        {
            var t2a:LambdaTerm,t2b:LambdaTerm:|t2==Application(t2a,t2b);
            LambdaEquivalence'(t1a,t2a,x1,x2,id1,id2);
            LambdaEquivalence'(t1b,t2b,x1,x2,id1,id2);

        }
}


lemma AlphaCongruenceLambda(y:Id, t1:LambdaTerm, t2:LambdaTerm)
    requires alphaEquivalence(t1, t2)
    ensures alphaEquivalence(Lambda(y, t1), Lambda(y, t2))
{
    assert []+[y]==[y]==[y]+[];
    AlphaCongruenceLambda'( t1, t2,y, [], []);
}

lemma AlphaCongruenceLambda'(t1:LambdaTerm, t2:LambdaTerm,y:Id, id1:seq<Id>, id2:seq<Id>)
    requires alphaEquivalence'(t1, t2, id1, id2)
    ensures alphaEquivalence'(t1, t2, [y]+id1, [y]+id2)
    decreases minim(lHeight(t1), lHeight(t2))
{
    match t1 {
        case Var(x) => {
            var z :| t2 == Var(z);
            var r1:=findId(id1, x);
            var r2:=findId(id2, z);
            
            var id1':=[y]+id1;
            var id2':=[y]+id2;
            var r1':=findId(id1', x);
            var r2':=findId(id2', z);

            findId_prepend(id1, x, x);
            findId_prepend(id2, y, x);

            if r1 == None {
                assert x == z;
                if x == y {
                    assert id1'[0] == x;
                    assert r1' == Some(0);

                    assert id2'[0] == z;
                    assert r2' == Some(0);

                } else {
                    assert r1' == None;
                    assert r2' == None;
                }
            } else {
                var i1 :| r1 == Some(i1);
                var new_pos := i1 + 1;

                assert id1'[new_pos] == x;
                assert r1' == Some(new_pos);

                assert id2'[new_pos] == z;
                assert r2' == Some(new_pos);
            }
        }
        case Lambda(x, t1') => {
            var z, t2' :| t2 == Lambda(z, t2');
            AlphaCongruenceLambda'( t1', t2',y, id1+[x], id2+[z]);
            assert [y]+id1+[x] == [y] + (id1+[x]);
            assert [y]+id2+[z] == [y] + (id2+[z]);
        }
        case Application(t1a, t1b) => {
            var t2a, t2b :| t2 == Application(t2a, t2b);
            AlphaCongruenceLambda'( t1a, t2a,y, id1, id2);
            AlphaCongruenceLambda'( t1b, t2b,y, id1, id2);
        }
    }
}


// lemma AddingBanListIsAllowed(t1:LambdaTerm,x:Id,t2:LambdaTerm,ids:seq<Id>,ids2:seq<Id>)
//     requires allUnique(ids) && allUnique(ids2)
//      requires allUnique(ids)
//         requires var s1:=vars(t1);
//          allUnique(s1) && includes(ids,s1) && x in ids 
//     requires var s2:=vars(t2);
//          allUnique(s2)  && includes(ids,s2) && x in ids
//     ensures var ids':=reunion(ids,ids2);
//     alphaEquivalence(caSubstitution'(t1,x,t2,ids),caSubstitution'(t1,x,t2,ids'))
// {

// }
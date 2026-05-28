include "objects.dfy"
type Id= nat
datatype LambdaTerm = Var(id:Id) | Lambda(x:Id,t:LambdaTerm) | Application( t1:LambdaTerm, t2:LambdaTerm)

function bound(t:LambdaTerm):seq<Id>
    ensures allUnique(bound(t))
{
        match t
                case Var(_) => []
                case Lambda(x,t) => addition(x,bound(t))
                case Application(t1,t2) => reunion(bound(t1),bound(t2))
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

function free(t:LambdaTerm):seq<Id>
    ensures allUnique(free(t))
{
     match t
                case Var(x) => [x]
                case Lambda(x,t) => remove(free(t),x)
                case Application(t1,t2) => reunion(free(t1),free(t2))
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
    requires var s1:=vars(t);
        allUnique(s1) 
    requires var s2:=vars(t');
        allUnique(s2)

{
    var ids:=reunion(vars(t),vars(t'));
    reunionIncludesBothSets(vars(t),vars(t'));
    caSubstitution'(t,x,t',reunion(vars(t),vars(t')))
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

lemma CaSubstitution'OfVarDoesNotChangeHeight(t1:LambdaTerm, x:Id, t2:LambdaTerm, ids:seq<Id>)
    requires match t2 case Var(_) => true case _ => false
    requires allUnique(ids)
    requires includes(ids,vars(t1)) && includes(ids,vars(t2))
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
                // alpha-rename branch
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
    CaSubstitution'OfVarDoesNotChangeHeight(t1, x, t2, ids);
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


include "objects.dfy"
type Id= string 
datatype LambdaTerm = Var(name:string) | Lambda(x:Id,t:LambdaTerm) | Application( t1:LambdaTerm, t2:LambdaTerm)

function bound(t:LambdaTerm):seq<Id>
    ensures allUnique(bound(t))
{
        match t
                case Var(_) => []
                case Lambda(x,t) => addition(x,bound(t))
                case Application(t1,t2) => reunion(bound(t1),bound(t2))
}
function addition(x:Id,s:seq<Id>) : seq<Id>
    requires allUnique(s)
    ensures var s':=addition(x,s);
            allUnique(s') && x in s'
{
    if x in s then s
    else  assert !(x in s);
        assert x in (s+[x]);
        assert allUnique(s+[x]); 
        s+[x]
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
ghost predicate isGoodForWork(s:seq<Id>)
    requires allUnique(s)
{
    forall str:Id:: ((str in s) && |str|>1 && str[0]=='n' && isStringAValidNumber(str[1..])) ==> stringToNat(str[1..])<|s|
}
lemma reunionIsGoodForWork(s1:seq<Id>,s2:seq<Id>)
    requires allUnique(s1) && isGoodForWork(s1)
    requires allUnique(s2) && isGoodForWork(s2)
    ensures allUnique(reunion(s1,s2)) && isGoodForWork(reunion(s1,s2))
{
    var s:=reunion(s1,s2);
    assert forall str:Id::(str in s1 || str in s2) ==> (str in s);
    assert forall str:Id::str in s1 ==> (str in s);
    assert |s|>=|s1|;
    assert |s|>=|s1| && |s|>=|s2|;
}
function addAnUniqueId(s:seq<Id>) : seq<Id>
    requires allUnique(s) && isGoodForWork(s)
    ensures allUnique(addAnUniqueId(s)) && isGoodForWork(addAnUniqueId(s))
{
    var str:="n"+natToString(|s|);
    natToStringThenStringToNatIdem(|s|);
    assert !(str in s);
    [str] +s
}
function remove(s:seq<Id>,x:Id):seq<Id>
    requires allUnique(s) 
    ensures ! (x in remove(s,x))
    ensures allUnique(remove(s,x))
    ensures forall str:Id:: str in remove(s,x) ==> str in s
    ensures forall str:Id:: str in s && str!=x ==> str in remove(s,x)
    ensures |s|-1<=|remove(s,x)|<=|s|
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
function substitution(t:LambdaTerm,x:Id,t':LambdaTerm):LambdaTerm
{
    match t
        case Var(y) => if y==x then t' else Var(y)
        case Lambda(y,t1) => if y==x then t else   Lambda(y,substitution(t1,x,t'))
        case Application(t1,t2) => Application(substitution(t1,x,t'),substitution(t2,x,t'))
}

function caSubstitution(t:LambdaTerm,x:Id,t':LambdaTerm):LambdaTerm
    requires var s1:=vars(t);
        allUnique(s1) && isGoodForWork(s1)
    requires var s2:=vars(t');
        allUnique(s2) && isGoodForWork(s2)
    ensures var s:=vars(caSubstitution(t,x,t'));
        allUnique(s) && isGoodForWork(s)
{
    caSubstitution'(t,x,t',reunion(vars(t),vars(t')))
}

function caSubstitution'(t:LambdaTerm,x:Id,t':LambdaTerm,ids:seq<Id>):LambdaTerm
    requires forall str:Id::str in reunion(vars(t),vars(t')) ==> str in ids 
    requires allUnique(ids) && isGoodForWork(ids)
{
    match t
        case Var(y) => if y==x then t' else Var(y)
        case Lambda(y,t1) => if y==x then t else
                                if !(y in free(t')) then Lambda(y,caSubstitution'(t,x,t',ids))
                                    else
                                        var ids':=addAnUniqueId(ids);
                                        Lambda(ids'[0],caSubstitution'())
        case Application(t1,t2) => Application(substitution(t1,x,t'),substitution(t2,x,t'))
}
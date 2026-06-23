include "./../objects.dfy"

ghost predicate allUnique (s:seq<Id>) 
{
    forall id1:nat,id2:nat::(id1<id2<|s|) ==> s[id1]!=s[id2]
}

lemma ElementNotInallUnique (s:seq<Id>,x:Id)
    requires !(x in s)
    requires allUnique(s)
    ensures allUnique([x]+s)
{
}    

predicate includes(s1:seq<Id>,s2:seq<Id>)
    
{
    forall id2:nat::id2<|s2| ==> (exists id1:nat::id1<|s1| && s1[id1]==s2[id2])
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
        ElementNotInallUnique(remove(s[1..],x),s[0]);
        [s[0]]+remove(s[1..],x)

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
        && (forall str:Id::str in s1 || str in s2 ==> (str in s) ) 
        && |s| >= |s1| && |s| >= |s2| 
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

lemma NotInReunionSoNotInBoth(s1:seq<Id>,s2:seq<Id>,x:Id)
    requires allUnique(s1) && allUnique(s2)
    requires !(x in reunion(s1,s2))
    ensures !(x in s1) && !(x in s2)
{

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



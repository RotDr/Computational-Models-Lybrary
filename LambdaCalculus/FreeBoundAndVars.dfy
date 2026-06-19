include "./../objects.dfy"
include "SetsAndSequences.dfy"

function bound(t:LambdaTerm):set<Id>
{
        match t
                case Var(_) => {}
                case Lambda(x,t) => {x}+bound(t)
                case Application(t1,t2) => bound(t1)+bound(t2)
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

lemma NotInFreeAndNotFoundInLambdaSoNotInFree(t:LambdaTerm,x:Id,y:Id)
    requires x!=y
    requires !(x in free(Lambda(y,t)))
    ensures !(x in free(t))
{

}

function vars(t:LambdaTerm):seq<Id>
    ensures allUnique(vars(t))
{
    match t
                case Var(x) => [x]
                case Lambda(x,t') => addition(x,vars(t'))
                case Application(t1,t2) => reunion(vars(t1),vars(t2))
}
function varsSet(t:LambdaTerm):set<Id>
    ensures forall x:Id:: (x in varsSet(t)) ==> (x in vars(t))
{
    match t 
            case Var(x) => {x}
            case Lambda(x,t') => {x}+varsSet(t')
            case Application(t1,t2) => varsSet(t1)+varsSet(t2)

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

lemma ASubLambdaOfAUniqueLambdaIsUnique(t:LambdaTerm)
    requires allUnique(vars(t))
    ensures match t 
                case Var(_)=> true 
                case Application(t1,t2) => allUnique(vars(t1)) && allUnique(vars(t2))
                case Lambda(_,t') => allUnique(vars(t'))
{

}

lemma notInVarsSoNotInFree(t:LambdaTerm,x:Id)
    requires !(x in vars(t))
    ensures !(x in free(t))
{

}


function lHeight(t:LambdaTerm):nat 
{
    match t
                case Var(x) => 1
                case Lambda(x,t') => 1+lHeight(t')
                case Application(t1,t2) => 1+max(lHeight(t1),lHeight(t2))
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

lemma findId_concat_notInLeft(W:seq<Id>, P:seq<Id>, y:Id)
    requires !(y in W)
    ensures findId(W+P, y) == (match findId(P, y) case Some(i) => Some(|W|+i) case None => None)
    decreases |P|
{
    if P == [] {
        assert W + P == W;
    } else {
        var p  := P[|P|-1];
        var P' := P[..|P|-1];
        assert P == P' + [p];
        assert W + P == (W + P') + [p];
        if p == y {
            assert findId(P, y) == Some(|P'|);
            assert |W + P'| == |W| + |P'|;
        } else {
            findId_concat_notInLeft(W, P', y);
            assert findId(P, y) == findId(P', y);
            assert findId(W + P, y) == findId(W + P', y);
        }
    }
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
include "LocallyNameless.dfy"
include "../BetaReduction.dfy"

lemma FromRefToLambdaBackToRef(t:RefLambdaTerm,named_t:LambdaTerm,nameless_t:RefLambdaTerm)
    requires locallyClosed(t)
    requires named_t==fromRefToLambda(t)
    requires nameless_t==fromLambdaToRef(named_t)
    ensures nameless_t==t
{
    IncludesItself(freeVarsSeq(t));
    assert includes(freeVarsSeq(t),freeVarsSeq(t));
    FromRefToLambdaBackToRef'(t,named_t,freeVarsSeq(t),[],nameless_t,[]);
}

lemma FromRefToLambdaBackToRef'(t:RefLambdaTerm,
    named_t:LambdaTerm,ids1:seq<Id>,lambda_names:seq<Id>,
    nameless_t:RefLambdaTerm,ids2:seq<Id>)
    requires locallyClosed'(t,|lambda_names|)
    requires lambda_names==ids2
    requires allUnique(ids1)
    requires includes(ids1,freeVarsSeq(t))
    requires allUnique(lambda_names)
    requires forall id:Id::id in ids1 ==>!(id in lambda_names)
    requires named_t==fromRefToLambda'(t,ids1,lambda_names)
    requires nameless_t==fromLambdaToRef'(named_t,ids2)
    ensures nameless_t==t
{
    match t 
        case FreeVar(x)=>{

            assert named_t==Var(x);
            assert x in freeVarsSeq(t);
            assert x in ids1;
            assert !(x in lambda_names);
            assert !(x in ids2);
            assert findId(ids2,x)==None;
            assert nameless_t==FreeVar(x);
        }
        case BoundVar(ref)=>{
            assert named_t==Var(lambda_names[ref]);
            var x:=lambda_names[ref];
            assert findId(lambda_names,x)==Some(ref);
            assert nameless_t==BoundVar(ref);
        }
        case App(t1,t2)=>{
            var named_t1:=fromRefToLambda'(t1,ids1,lambda_names);
            var named_t2:=fromRefToLambda'(t2,ids1,lambda_names);
            assert named_t==Application(named_t1,named_t2);
            var nameless_t1:=fromLambdaToRef'(named_t1,lambda_names);
            var nameless_t2:=fromLambdaToRef'(named_t2,lambda_names);
            assert nameless_t==App(nameless_t1,nameless_t2);

            reunionIncludesBothSets(freeVarsSeq(t1),freeVarsSeq(t2));

            FromRefToLambdaBackToRef'(t1,named_t1,ids1,lambda_names
            ,nameless_t1,lambda_names);
            assert nameless_t1==t1;
            FromRefToLambdaBackToRef'(t2,named_t2,ids1,lambda_names
            ,nameless_t2,lambda_names);
            assert nameless_t2==t2;

        }
        case RefLambda(t')=>{
            var new_id:=addAnUniqueId(reunion(ids1,lambda_names))[0];
            var new_lambda_names:=lambda_names+[new_id];
            var named_t':=fromRefToLambda'(t',ids1,new_lambda_names);
            assert named_t==Lambda(new_id,named_t');

            var nameless_t':=fromLambdaToRef'(named_t',new_lambda_names);
            assert nameless_t==RefLambda(nameless_t');
           
            FromRefToLambdaBackToRef'(t',named_t',ids1,new_lambda_names,
            nameless_t',new_lambda_names);

            assert nameless_t'==t';
        }

}

lemma FromLambdaToRefBackToLambda(t:LambdaTerm,nameless_t:RefLambdaTerm,named_t:LambdaTerm)
    requires nameless_t==fromLambdaToRef(t)
    requires locallyClosed(nameless_t)
    requires named_t==fromRefToLambda(nameless_t)
    ensures alphaEquivalence(t,named_t)
{
    IncludesItself(freeVarsSeq(nameless_t));
    assert includes(freeVarsSeq(nameless_t),freeVarsSeq(nameless_t));
    FromLambdaToRefBackToLambda'(t,nameless_t,[],named_t,freeVarsSeq(nameless_t),[]);
}

lemma FromLambdaToRefBackToLambda'(t:LambdaTerm,
    nameless_t:RefLambdaTerm,ids1:seq<Id>,
    named_t:LambdaTerm,ids2:seq<Id>,lambda_names:seq<Id>)

    requires nameless_t==fromLambdaToRef'(t,ids1)
    requires locallyClosed'(nameless_t,|lambda_names|)
    requires |ids1|==|lambda_names|
    requires allUnique(ids2)
    requires includes(ids2,freeVarsSeq(nameless_t))
    requires forall id:Id::id in ids2 ==>!(id in lambda_names)
    requires allUnique(lambda_names)
    requires named_t==fromRefToLambda'(nameless_t,ids2,lambda_names)
    ensures alphaEquivalence'(t,named_t,ids1,lambda_names)
{
    match t 
        case Var(x) =>
        {
            match findId(ids1,x)
                case None=>
                {
                    assert x in freeVarsSeq(nameless_t);
                    var j:nat :| j<|ids2| && ids2[j]==x;   
                    assert x in ids2;
                    assert !(x in lambda_names);
                    assert findId(lambda_names,x)==None;
                }
                case Some(refId)=>
                {
                    assert nameless_t==BoundVar(refId);
                    assert allUnique(lambda_names);
                    var new_id:=lambda_names[refId];
                    assert named_t==Var(new_id);
                    assert findId(lambda_names,new_id)==Some(refId);
                }
        }
        case Lambda(x,t')=>
        {
            var new_ids1:=ids1+[x];
            var nameless_t':=fromLambdaToRef'(t',new_ids1);
            assert nameless_t==RefLambda(nameless_t');

            var new_id:=addAnUniqueId(reunion(ids2,lambda_names))[0];
            var new_lambda_names:=lambda_names+[new_id];
            var named_t':=fromRefToLambda'(nameless_t',ids2,new_lambda_names);

            FromLambdaToRefBackToLambda'(t',nameless_t',new_ids1,named_t',ids2,new_lambda_names);
            assert alphaEquivalence'(t',named_t',new_ids1,new_lambda_names);
        }
        case Application(t1,t2)=>
        {
            var nameless_t1:=fromLambdaToRef'(t1,ids1);
            var nameless_t2:=fromLambdaToRef'(t2,ids1); 
            assert nameless_t==App(nameless_t1,nameless_t2);

            var named_t1:=fromRefToLambda'(nameless_t1,ids2,lambda_names);
            var named_t2:=fromRefToLambda'(nameless_t2,ids2,lambda_names);
            assert named_t==Application(named_t1,named_t2);

            reunionIncludesBothSets(freeVarsSeq(nameless_t1),freeVarsSeq(nameless_t2));
            FromLambdaToRefBackToLambda'(t1,nameless_t1,ids1,named_t1,ids2,lambda_names);
            FromLambdaToRefBackToLambda'(t2,nameless_t2,ids1,named_t2,ids2,lambda_names);

            assert alphaEquivalence'(t1,named_t1,ids1,lambda_names);
            assert alphaEquivalence'(t2,named_t2,ids1,lambda_names);
        }

}

lemma theCountIsTheSameRef(t:RefLambdaTerm,named_t:LambdaTerm)
    requires locallyClosed(t) 
    requires named_t==fromRefToLambda(t)
    ensures numberOfRedexes(t)==numberOfPossibleReducations(named_t)
{
    TheCountIsTheSameRef'(t,freeVarsSeq(t),[],named_t);
}

lemma TheCountIsTheSameRef'(t:RefLambdaTerm,ids:seq<Id>,lambda_names:seq<Id>,named_t:LambdaTerm)
    requires locallyClosed'(t,|lambda_names|)
    requires allUnique(ids) 
    requires forall id:Id::id in ids ==>!(id in lambda_names)
    requires allUnique(lambda_names)
    requires fromRefToLambda'(t,ids,lambda_names)==named_t
    ensures  numberOfRedexes(t)==numberOfPossibleReducations(named_t)
{
    match t 
        case RefLambda(t') =>
        {
            var new_ids:=addAnUniqueId(reunion(ids,lambda_names));
            var named_t':=fromRefToLambda'(t',ids,lambda_names+[new_ids[0]]);
            TheCountIsTheSameRef'(t',ids,lambda_names+[new_ids[0]],named_t');
        }
        case FreeVar(_)=>
        {
            assert exists x:Id::named_t==Var(x);

        }
        case BoundVar(_)=>
        {
            assert exists x:Id::named_t==Var(x);
        }
        case App(t1,t2)=>
        {
            var named_t1:=fromRefToLambda'(t1,ids,lambda_names);
            var named_t2:=fromRefToLambda'(t2,ids,lambda_names);
            TheCountIsTheSameRef'(t1,ids,lambda_names,named_t1);
            TheCountIsTheSameRef'(t2,ids,lambda_names,named_t2);
        }

}
lemma TheCountIsTheSameNamedLambda(t:LambdaTerm,nameless_t:RefLambdaTerm)
    requires nameless_t==fromLambdaToRef(t)
    ensures numberOfPossibleReducations(t)==numberOfRedexes(nameless_t)
{
    assert nameless_t==fromLambdaToRef'(t,[]);
    TheCountIsTheSameNamedLambda'(t,nameless_t,[]);
}

lemma TheCountIsTheSameNamedLambda'(t:LambdaTerm,nameless_t:RefLambdaTerm,ids:seq<Id>)
    requires nameless_t==fromLambdaToRef'(t,ids)
    ensures numberOfPossibleReducations(t)==numberOfRedexes(nameless_t)
{
    match t 
        case Var(_) =>{
            assert numberOfPossibleReducations(t)==0;
            assert exists x:nat:: nameless_t==FreeVar(x) || nameless_t==BoundVar(x);
            assert numberOfRedexes(nameless_t)==0;
        }
        case Application(t1,t2)=>{
            var nameless_t1:=fromLambdaToRef'(t1,ids);
            var nameless_t2:=fromLambdaToRef'(t2,ids);

            TheCountIsTheSameNamedLambda'(t1,nameless_t1,ids);
            TheCountIsTheSameNamedLambda'(t2,nameless_t2,ids);

        
            if (isCorrectForBetaReduction(t))
            {
                var t':LambdaTerm,x:Id:| t1==Lambda(x,t');
                var nameless_t':=fromLambdaToRef'(t',ids);
                assert isRefAppLambda(nameless_t);
            }
        }
        case Lambda(x,t')=>{
            var nameless_t':=fromLambdaToRef'(t',ids+[x]);
            TheCountIsTheSameNamedLambda'(t',nameless_t',ids+[x]);
        }

}

// lemma theBetaReductionStepisTheSameRef(t:RefLambdaTerm,choice:nat,named_t:LambdaTerm)
//     requires var l_total_count:=numberOfRedexes(t);
//         l_total_count!=0 && l_total_count>choice 
//     requires locallyClosed(t)
//     ensures 0<numberOfPossibleReducations(named_t) &&
//           choice<numberOfPossibleReducations(named_t) &&
//           fromLambdaToRef(betaReductionStep(named_t,choice))==refBetaReductionStep(t,choice)
// {
//     assume false;
// }

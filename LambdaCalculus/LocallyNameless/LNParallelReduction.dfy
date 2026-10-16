include "LocallyNameless.dfy"

ghost predicate refParallelReduction(t1:RefLambdaTerm,t2:RefLambdaTerm)
    decreases refLHeight(t1)
{
    (t1==t2 && match t1 
            case FreeVar(_)=> true
            case _ => false ) ||
    (match t1 
        case RefLambda(t1')=>(match t2
                                case RefLambda(t2')=>( exists L:seq<Id>:: allUnique(L) && forall x:Id::!(x in L)==>
                                && refParallelReduction(open'(0,x,t1'),open'(0,x,t2')))
                                case _=> false)
        case _=> false ) ||
    (match t1 
        case App(t1a,t2a)=> 
        (
            match t1a 
                case RefLambda(t1a')=> 
                assert forall x:Id:: refLHeight(t1a')==refLHeight(open'(0,x,t1a'));
                assert refLHeight(t1a')<refLHeight(t1);
                    (
                    exists L:seq<Id>::  (allUnique(L) && forall x:Id::!(x in L)==>(exists  t1':RefLambdaTerm,t2':RefLambdaTerm
                    ::refParallelReduction(open'(0,x,t1a'),open'(0,x,t1')) && refParallelReduction(t2a,t2') &&
                        t2==opening(t1',0,t2')))
                )
                case _=> false
        )
        case _=> false) ||
    (match t1 
        case App(t1a,t1b)=> (match t2 
                                case App(t2a,t2b)=>
                                (refParallelReduction(t1a,t2a) && refParallelReduction(t1b,t2b))
                                case _=> false)
        case _=> false)
}

ghost predicate refRule1 (t1:RefLambdaTerm,t2:RefLambdaTerm)
{
     (t1==t2 && match t1 
            case FreeVar(_)=> true
            case _ => false )
}
ghost predicate refRule2 (t1:RefLambdaTerm,t2:RefLambdaTerm)
{
     match t1 
        case RefLambda(t1')=>(match t2
                                case RefLambda(t2')=>( exists L:seq<Id>:: allUnique(L) && forall x:Id::!(x in L)==>
                                && refParallelReduction(open'(0,x,t1'),open'(0,x,t2')))
                                case _=> false)
        case _=>false
}
ghost predicate refRule3(t1:RefLambdaTerm,t2:RefLambdaTerm)
{
    match t1 
        case App(t1a,t2a)=> 
        (
            match t1a 
                case RefLambda(t1a')=> 
                assert forall x:Id:: refLHeight(t1a')==refLHeight(open'(0,x,t1a'));
                assert refLHeight(t1a')<refLHeight(t1);
                    (
                    exists L:seq<Id>::  (allUnique(L) && forall x:Id::!(x in L)==>(exists  t1':RefLambdaTerm,t2':RefLambdaTerm
                    ::refParallelReduction(open'(0,x,t1a'),open'(0,x,t1')) && refParallelReduction(t2a,t2') &&
                        t2==opening(t1',0,t2')))
                )
                case _=> false
        )
        case _=> false
}

ghost predicate refRule4(t1:RefLambdaTerm,t2:RefLambdaTerm)
{
    match t1 
        case App(t1a,t1b)=> (match t2 
                                case App(t2a,t2b)=>
                                (refParallelReduction(t1a,t2a) && refParallelReduction(t1b,t2b))
                                case _=> false)
        case _=> false
}
lemma RefParallelReductionIsBasedOnFourRules(t1:RefLambdaTerm,t2:RefLambdaTerm)
    requires refParallelReduction(t1,t2)
    ensures refRule1(t1,t2) || refRule2(t1,t2) || refRule3(t1,t2) || refRule4(t1,t2)
{

}

lemma RefFourRulesDefineParallelReduction(t1:RefLambdaTerm,t2:RefLambdaTerm)
    requires refRule1(t1,t2) || refRule2(t1,t2) || refRule3(t1,t2) || refRule4(t1,t2)
    ensures refParallelReduction(t1,t2)
{

}


lemma refParaReductionReflexive(t:RefLambdaTerm)
    requires locallyClosed(t)
    decreases refLHeight(t)
    ensures refParallelReduction(t,t)
{
    match t 
        case FreeVar(_) => {}
        case BoundVar(_) => {assert false;}
        case App(t1a,t2a) =>{
            refParaReductionReflexive(t1a);
            refParaReductionReflexive(t2a);
            assert refParallelReduction(t1a,t1a) && refParallelReduction(t2a,t2a);
        }
        case RefLambda(t' )=>{

            forall x:Id | !(x in freeVarsSeq(t'))
            ensures refParallelReduction(open'(0,x,t'),open'(0,x,t'))
            {
                OpeningIsClosed(t',x);
                refParaReductionReflexive(open'(0,x,t'));
            }
            assert forall x:Id::!(x in freeVarsSeq(t'))==> refParallelReduction(open'(0,x,t'),open'(0,x,t'));
            var L:=freeVarsSeq(t');
            
        }
}


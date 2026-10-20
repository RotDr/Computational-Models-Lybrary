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
                    exists L:seq<Id>,t1':RefLambdaTerm,t2':RefLambdaTerm::t2==opening(t1',0,t2') && refParallelReduction(t2a,t2') &&  allUnique(L) && (forall x:Id::!(x in L)==>
                    refParallelReduction(open'(0,x,t1a'),open'(0,x,t1')) 
                        )
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
lemma Rule2Intro(t:RefLambdaTerm, t':RefLambdaTerm, L:seq<Id>)
    requires allUnique(L)
    requires forall y:Id :: !(y in L) ==> refParallelReduction(open'(0,y,t),open'(0,y,t'))
    ensures refParallelReduction(RefLambda(t),RefLambda(t'))
{

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
                   exists L:seq<Id>,t1':RefLambdaTerm,t2':RefLambdaTerm::t2==opening(t1',0,t2') && refParallelReduction(t2a,t2') &&  allUnique(L) && (forall x:Id::!(x in L)==>
                    refParallelReduction(open'(0,x,t1a'),open'(0,x,t1')) 
                        )
                )
                case _=> false
        )
        case _=> false
}

lemma Rule3Intro(t1:RefLambdaTerm, t2:RefLambdaTerm, t1':RefLambdaTerm, t2':RefLambdaTerm, L:seq<Id>)
    requires allUnique(L)
    requires refParallelReduction(t2,t2')
    requires forall x:Id :: !(x in L) ==> refParallelReduction(open'(0,x,t1),open'(0,x,t1'))
    ensures refParallelReduction(App(RefLambda(t1),t2), opening(t1',0,t2'))
{

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

lemma ParBodyViaClose(t:RefLambdaTerm, t':RefLambdaTerm, x:Id, y:Id)
    requires !(x in freeVarsSeq(t))
    requires locallyClosed'(t,1)
    requires refParallelReduction(open'(0,x,t), t')
    decreases refLHeight(t)
    ensures  refParallelReduction(open'(0,y,t), open'(0,y,close(t',x)))
{
    OpeningIsClosed'(t,x,0);
    assert locallyClosed(open'(0,x,t));
    ParReductionPreservesLocallyClosed(open'(0,x,t), t');
    assert locallyClosed(t');


    CloseOpenIsSubstitution(t',x,y,0);
    assert close(t',x) == close'(t',x,0);
    assert open'(0,y,close(t',x)) == LNSubstitution(t',x,FreeVar(y));

    SubstitutionIntro(t,x,FreeVar(y),0);
    OpeningWithFreeVarIsOpen(t,0,y);
    assert open'(0,y,t) == LNSubstitution(open'(0,x,t),x,FreeVar(y));


    assert refRule1(FreeVar(y),FreeVar(y));
    RefFourRulesDefineParallelReduction(FreeVar(y),FreeVar(y));
    assert locallyClosed(FreeVar(y));

    ParSubstitution(open'(0,x,t), t', FreeVar(y), FreeVar(y), x);
}

lemma ParOpening(t:RefLambdaTerm, t':RefLambdaTerm, u:RefLambdaTerm, u':RefLambdaTerm, L:seq<Id>)
    requires allUnique(L)
    requires forall y:Id :: !(y in L) ==> refParallelReduction(open'(0,y,t),open'(0,y,t'))
    requires refParallelReduction(u,u')
    requires locallyClosed(u) && locallyClosed(u')
    ensures  refParallelReduction(opening(t,0,u), opening(t',0,u'))
{
    var L:seq<Id>:|allUnique(L) && forall y:Id::!(y in L) ==> refParallelReduction(open'(0,y,t),open'(0,y,t'));
    var L1:=freeVarsSeq(t);
    var L2:=freeVarsSeq(t');
    var L3:=reunion(reunion(L1,L2),L);
    forall y:Id|!(y in L3)
        ensures refParallelReduction(opening(t,0,u), opening(t',0,u')) 
    {
        NotInReunionSoNotInBoth(reunion(L1,L2),L,y);
        NotInReunionSoNotInBoth(L1,L2,y);

        assert  refParallelReduction(open'(0,y,t),open'(0,y,t'));

        SubstitutionIntro(t,y,u,0);
        SubstitutionIntro(t',y,u',0);

        assert opening(t,0,u)==LNSubstitution(open'(0,y,t),y,u);
        assert opening(t',0,u')==LNSubstitution(open'(0,y,t'),y,u');

        ParSubstitution(open'(0,y,t),open'(0,y,t'),u,u',y);

        
    }
    var y:=addAnUniqueId(L3)[0];
    assert refParallelReduction(opening(t,0,u), opening(t',0,u'));
}

lemma FreeVarsRemainTheSameDuringParReduction(t:RefLambdaTerm, t':RefLambdaTerm)
    requires refParallelReduction(t,t')
    ensures freeVarsSeq(t)==freeVarsSeq(t')
{
    if (refRule1(t,t'))
    {

    }
    else
    {
        if (refRule2(t,t'))
        {
            assume false;
        } 
        else 
        {
            if (refRule3(t,t'))
            {
                assume false;
            }
            else 
            {
                assert refRule4(t,t');
                assume false;
            }
        }
    }
}
lemma ParSubstitution(t:RefLambdaTerm, t':RefLambdaTerm,
                      u:RefLambdaTerm, u':RefLambdaTerm, x:Id)
    requires refParallelReduction(t, t')
    requires refParallelReduction(u, u')
    requires locallyClosed(u)
    requires locallyClosed(u')
    ensures  refParallelReduction(LNSubstitution(t, x, u),
                                  LNSubstitution(t', x, u'))
    decreases refLHeight(t)
{

    if (refRule1(t,t'))
    {

    }
    else
    {
        if (refRule2(t,t'))
        {
            match t 
                case RefLambda(t1)=>
                {
                    match t' 
                        case RefLambda(t1')=>
                        {
                            var L:seq<Id>:|allUnique(L) && forall y:Id::!(y in L) ==> refParallelReduction(open'(0,y,t1),open'(0,y,t1'));
                            var L2:seq<Id>:= if (x in L) then L else L+[x];
                            assert allUnique(L2);
                            assert x in L2;
                            forall y:Id| !(y in L2)
                                ensures refParallelReduction(open'(0,y,LNSubstitution(t1,x,u)),open'(0,y,LNSubstitution(t1',x,u')))
                            {
                                assert refParallelReduction(open'(0,y,t1),open'(0,y,t1'));
                                assert refLHeight(open'(0,y,t1))==refLHeight(t1);
                                ParSubstitution(open'(0,y,t1),open'(0,y,t1'),u,u',x);
                                SubstitutionAndOpening(t1,x,y,u,0);
                                SubstitutionAndOpening(t1',x,y,u',0);
                            }
                        }
                }
        }
        else 
        {
            if (refRule3(t,t'))
            {
                match t 
                    case App(t1,t2)=>
                    {
                        match t1 
                            case RefLambda(t1a)=>
                            {
                                var L:seq<Id>,v1:RefLambdaTerm,v2:RefLambdaTerm:|t'==opening(v1,0,v2) && refParallelReduction(t2,v2) &&  allUnique(L) && (forall x:Id::!(x in L)==>
                                refParallelReduction(open'(0,x,t1a),open'(0,x,v1))); 

                                var L1:seq<Id>:= if x in L then L else L+[x];
                                assert allUnique(L1);
                                assert x in L1;
                                assert refLHeight(t2)<refLHeight(t);
                                ParSubstitution(t2,v2,u,u',x);
                                forall y:Id|!(y in L1)
                                    ensures refParallelReduction(open'(0,y,LNSubstitution(t1a,x,u)),open'(0,y,LNSubstitution(v1,x,u')))
                                {
                                    assert y!=x;
                                    assert refParallelReduction(open'(0,y,t1a),open'(0,y,v1));
                                    assert refLHeight(open'(0,y,t1a))==refLHeight(t1a);
                                    assert refLHeight(t1a)<refLHeight(t);
                                    ParSubstitution(open'(0,y,t1a),open'(0,y,v1),u,u',x);
                                    SubstitutionAndOpening(t1a,x,y,u,0);
                                    SubstitutionAndOpening(v1,x,y,u',0);
                                }
                                assert locallyClosed'(u',0);
                                SubstitutionOpen(v1,x,u',v2,0);

                                assert LNSubstitution(t,x,u)==App(RefLambda(LNSubstitution(t1a,x,u)),LNSubstitution(t2,x,u));
                                assert LNSubstitution(t',x,u')==opening(LNSubstitution(v1,x,u'),0,LNSubstitution(v2,x,u'));
                                assert refParallelReduction(LNSubstitution(t2,x,u),LNSubstitution(v2,x,u'));
                                assert forall y:Id::!(y in L1)==>
                                    refParallelReduction(open'(0,y,LNSubstitution(t1a,x,u)),open'(0,y,LNSubstitution(v1,x,u')));

                                assert refRule3(LNSubstitution(t,x,u),LNSubstitution(t',x,u'));
                            }
                    }
            }
            else 
            {
                assert refRule4(t,t');
                match t 
                    case App(t1,t2)=>
                    {
                        match t'
                            case App(t1',t2')=> 
                            {
                                assert refParallelReduction(t1,t1');
                                assert refParallelReduction(t2,t2');
                                ParSubstitution(t1,t1',u,u',x);
                                ParSubstitution(t2,t2',u,u',x);
                            }
                    }
            }
        }
    }
}


lemma ParallelReductionPreservesClosure(t1: RefLambdaTerm, t2: RefLambdaTerm)
    requires locallyClosedCanon(t1) 
    requires refParallelReduction(t1,t2)
    ensures locallyClosedCanon(t2)
    decreases refLHeight(t1)
{
    if (refRule1(t1,t2)) 
    {

    }
    else 
    {
        if (refRule2(t1,t2))
        {
                assert locallyClosedCanon(t1);
                match t1
                    case RefLambda(t1')=>{
                        match t2 
                            case RefLambda(t2')=>{
                                var L:seq<Id> :|allUnique(L) && forall x:Id::!(x in L)==> refParallelReduction(open'(0,x,t1'),open'(0,x,t2'));
                                var L2:seq<Id>:|allUnique(L2) && forall x:Id::!(x in L2)==>locallyClosedCanon(open'(0,x,t1'));

                                var L3:=reunion(L,L2);
                                forall x:Id| !(x in L3) 
                                    ensures locallyClosedCanon(open'(0,x,t2'))
                                {
                                    NotInReunionSoNotInBoth(L,L2,x);
                                    assert !(x in L);
                                    assert !(x in L2);
                                    assert forall x:Id::!(x in L)==> refParallelReduction(open'(0,x,t1'),open'(0,x,t2'));
                                    assert forall x:Id::!(x in L2)==>locallyClosedCanon(open'(0,x,t1'));
                                    assert locallyClosedCanon(open'(0,x,t1'));
                                    assert refParallelReduction(open'(0,x,t1'),open'(0,x,t2'));
                                    ParallelReductionPreservesClosure(open'(0,x,t1'),open'(0,x,t2'));
                                    
                                }
                            }
                    }        
        }
        else
        {
            if (refRule3(t1,t2))
            {
                match t1
        case App(t1a,t2a) =>
        {
            match t1a
                case RefLambda(t1a') =>
                {
                    var L:seq<Id>, t1':RefLambdaTerm, t2':RefLambdaTerm :|
                        t2==opening(t1',0,t2') && refParallelReduction(t2a,t2')
                        && allUnique(L)
                        && (forall x:Id :: !(x in L) ==>
                                refParallelReduction(open'(0,x,t1a'),open'(0,x,t1')));

                    assert locallyClosedCanon(t1a) && locallyClosedCanon(t2a);
                    assert locallyClosedCanon(RefLambda(t1a'));
                    var L2:seq<Id> :| allUnique(L2) &&
                        forall x:Id :: !(x in L2) ==> locallyClosedCanon(open'(0,x,t1a'));


                    ParallelReductionPreservesClosure(t2a, t2');
                    LocalClosingEquivalence1(t2');
                    assert locallyClosed(t2');


                    var avoid := reunion(reunion(L,L2), freeVarsSeq(t1'));
                    var x:Id := addAnUniqueId(avoid)[0];
                    assert !(x in avoid);
                    NotInReunionSoNotInBoth(reunion(L,L2), freeVarsSeq(t1'), x);
                    NotInReunionSoNotInBoth(L, L2, x);
                    assert !(x in L) && !(x in L2) && !(x in freeVarsSeq(t1'));

    
                    assert locallyClosedCanon(open'(0,x,t1a'));
                    assert refParallelReduction(open'(0,x,t1a'),open'(0,x,t1'));
                    ParallelReductionPreservesClosure(open'(0,x,t1a'), open'(0,x,t1'));
                    LocalClosingEquivalence1(open'(0,x,t1'));
                    assert locallyClosed(open'(0,x,t1'));

  
                    SubstitutionIntro(t1', x, t2', 0);
                    RefSubsitutionClosure(open'(0,x,t1'), x, t2');
                    assert locallyClosed(t2);
                    LocalClosingEquivalence2(t2);
                }
                case _ => { assert false; }
        }
        case _ => { assert false; }
            }

        }
        
    }
}

lemma ParReductionPreservesLocallyClosed(t:RefLambdaTerm, t':RefLambdaTerm)
    requires locallyClosed(t)
    requires refParallelReduction(t,t')
    ensures  locallyClosed(t')
{
    LocalClosingEquivalence2(t);
    ParallelReductionPreservesClosure(t,t');
    LocalClosingEquivalence1(t');
}
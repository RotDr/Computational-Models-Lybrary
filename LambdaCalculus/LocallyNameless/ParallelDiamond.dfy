include "LNParallelReduction.dfy"

lemma Rule2Diamond(t1:RefLambdaTerm, t2:RefLambdaTerm, x:Id, t3:RefLambdaTerm, y:Id)
    requires locallyClosed'(t1,1) && locallyClosed'(t2,1)
    requires !(x in freeVarsSeq(t1)) && !(x in freeVarsSeq(t2))
    requires refParallelReduction(open'(0,x,t1),t3)
    requires refParallelReduction(open'(0,x,t2),t3)
    ensures refParallelReduction(open'(0,y,t1),open'(0,y,close(t3,x)))
    ensures refParallelReduction(open'(0,y,t2),open'(0,y,close(t3,x)))
{
    ParBodyViaClose(t1,t3,x,y);
    ParBodyViaClose(t2,t3,x,y);
}

lemma Rule3Diamond(t:RefLambdaTerm,t1:RefLambdaTerm,t2:RefLambdaTerm)
    requires locallyClosed(t)
    requires refRule3(t,t1)
    requires refRule3(t,t2)
    decreases refLHeight(t), 1
    ensures exists t3:RefLambdaTerm::refParallelReduction(t1,t3) && refParallelReduction(t2,t3)
{
    var ta':RefLambdaTerm,tb:RefLambdaTerm:|t==App(RefLambda(ta'),tb);
    var t1u:RefLambdaTerm,t1v:RefLambdaTerm,L1:seq<Id>:|t1==opening(t1u,0,t1v) && 
    refParallelReduction(tb,t1v)
    && allUnique(L1) 
    && forall x:Id::!(x in L1) ==> refParallelReduction(open'(0,x,ta'),open'(0,x,t1u));

    var t2u:RefLambdaTerm,t2v:RefLambdaTerm,L2:seq<Id>:|t2==opening(t2u,0,t2v) && 
    refParallelReduction(tb,t2v)
    && allUnique(L2) 
    && forall x:Id::!(x in L2) ==> refParallelReduction(open'(0,x,ta'),open'(0,x,t2u));


    assert refLHeight(tb)<refLHeight(t);
    ParDiamond(tb,t1v,t2v);
    var t3v:RefLambdaTerm:|refParallelReduction(t1v,t3v) && refParallelReduction(t2v,t3v);

    var L3:=reunion(reunion(L1,L2),freeVarsSeq(t));
    var L4:=reunion(L3,reunion(freeVarsSeq(t1u),freeVarsSeq(t2u)));
    var x:Id:=addAnUniqueId(L4)[0];
    NotInReunionSoNotInBoth(L3,reunion(freeVarsSeq(t1u),freeVarsSeq(t2u)),x);
    NotInReunionSoNotInBoth(freeVarsSeq(t1u),freeVarsSeq(t2u),x);
    NotInReunionSoNotInBoth(reunion(L1,L2),freeVarsSeq(t),x);
    NotInReunionSoNotInBoth(L1,L2,x);

    assert locallyClosed(RefLambda(ta'));
    assert locallyClosed'(ta',1);
    IfWeForgetThatIsOpenedItThenIsClosed'(ta',x,1);
    ReductBodyIsClosed(ta',t1u,x);
    ReductBodyIsClosed(ta',t2u,x);

    assert refLHeight(ta')<refLHeight(t);
    assert !(x in L2);
    assert forall x:Id::!(x in L2) ==> refParallelReduction(open'(0,x,ta'),open'(0,x,t2u));
    assert refParallelReduction(open'(0,x,ta'),open'(0,x,t2u));
    assert !(x in L1);
    assert forall x:Id::!(x in L1) ==> refParallelReduction(open'(0,x,ta'),open'(0,x,t1u));
    assert refParallelReduction(open'(0,x,ta'),open'(0,x,t1u));
    ParDiamond(open'(0,x,ta'),open'(0,x,t1u),open'(0,x,t2u));
    var opened_t3u:RefLambdaTerm:|refParallelReduction(open'(0,x,t1u),opened_t3u) && 
                                    refParallelReduction(open'(0,x,t2u),opened_t3u);

    var t3u:RefLambdaTerm:=close(opened_t3u,x);

    forall y:Id|!(y in [])
        ensures refParallelReduction(open'(0,y,t1u),open'(0,y,t3u))
        ensures refParallelReduction(open'(0,y,t2u),open'(0,y,t3u))
    {
        ParBodyViaClose(t1u,opened_t3u,x,y);
        ParBodyViaClose(t2u,opened_t3u,x,y);
    }

    ParReductionPreservesLocallyClosed(tb,t1v);
    ParReductionPreservesLocallyClosed(t1v,t3v);
    assert locallyClosed(t1v) && locallyClosed(t3v);
    ParOpening(t1u,t3u,t1v,t3v,[]);

    ParReductionPreservesLocallyClosed(tb,t2v);
    assert locallyClosed(t2v);
    ParOpening(t2u,t3u,t2v,t3v,[]);

    var t3:=opening(t3u,0,t3v);
    assert refParallelReduction(t1,t3);
    assert refParallelReduction(t2,t3);
}

lemma MixedRulesDiamond(t:RefLambdaTerm, t1:RefLambdaTerm, t2:RefLambdaTerm)
    requires locallyClosed(t)
    requires refRule3(t,t1)
    requires refRule4(t,t2)
    ensures exists t3:RefLambdaTerm :: refParallelReduction(t1,t3) && refParallelReduction(t2,t3)
    decreases refLHeight(t), 1
{
    assert refRule3(t,t1);
    match t
        case App(ta,tb)=>
        {
            var t2a:RefLambdaTerm,t2b:RefLambdaTerm:|t2==App(t2a,t2b);
            assert refParallelReduction(ta,t2a);
            assert refParallelReduction(tb,t2b);
            match ta 
                case RefLambda(ta')=>
                {
                    assert refRule2(ta,t2a);
                    var t2a':RefLambdaTerm:|t2a==RefLambda(t2a');
                    var L:seq<Id>:|allUnique(L) && forall x:Id::!(x in L) ==> refParallelReduction(open'(0,x,ta'),open'(0,x,t2a'));
                    assert refRule3(t,t1);
                    var L1:seq<Id>,u:RefLambdaTerm,v:RefLambdaTerm:|t1==opening(u,0,v) && 
                    refParallelReduction(tb,v) &&
                    allUnique(L1) 
                    &&( forall x:Id::!(x in L1) ==> refParallelReduction(open'(0,x,ta'),open'(0,x,u)));

                    assert locallyClosed(tb);
                    ParDiamond(tb,t2b,v);
                    var t3b:RefLambdaTerm:|refParallelReduction(t2b,t3b) && refParallelReduction(v,t3b);


                    var L2:=reunion(L,L1);


                    var L3:=reunion(freeVarsSeq(t2a'),freeVarsSeq(u));
                    var L4:=reunion(L2,L3);
                    var x:Id:=addAnUniqueId(L4)[0];
                    

                    NotInReunionSoNotInBoth(L2,L3,x);
                    NotInReunionSoNotInBoth(L,L1,x);
                    NotInReunionSoNotInBoth(freeVarsSeq(t2a'),freeVarsSeq(u),x);
                    
                    assert locallyClosed'(ta,0);
                    assert locallyClosed'(ta',1);
                    assert refParallelReduction(open'(0,x,ta'),open'(0,x,t2a'));
                    assert refParallelReduction(open'(0,x,ta'),open'(0,x,u));
                    ReductBodyIsClosed(ta',u,x);
                    ReductBodyIsClosed(ta',t2a',x);

                    IfWeForgetThatIsOpenedItThenIsClosed(ta,x);
                    assert refLHeight(ta')<refLHeight(ta);
                    ParDiamond(open'(0,x,ta'),open'(0,x,t2a'),open'(0,x,u));

                    var opened_t3a':RefLambdaTerm:|refParallelReduction(open'(0,x,u),opened_t3a') && refParallelReduction(open'(0,x,t2a'),opened_t3a');
                    var t3a':RefLambdaTerm:=close(opened_t3a',x);

                    assert locallyClosed'(t2a',1);
                    assert locallyClosed'(u,1);
                    
                    forall y:Id | !(y in [])
                        ensures refParallelReduction(open'(0,y,t2a'),open'(0,y,t3a')) && 
                            refParallelReduction(open'(0,y,u),open'(0,y,t3a'))
                    {
                        Rule2Diamond(u,t2a',x,opened_t3a',y);
                    }
                    Rule2Intro(u,t3a',[]);
                    Rule2Intro(t2a',t3a',[]);

                    ParReductionPreservesLocallyClosed(tb,v);
                    ParReductionPreservesLocallyClosed(v,t3b);
                    assert locallyClosed(t3b);
                    assert locallyClosed(v);
                    ParOpening(u,t3a',v,t3b,[]);

                    var t3:=opening(t3a',0,t3b);
                    assert refParallelReduction(t1,t3);


                    assert refParallelReduction(t2b,t3b);
                    assert forall y:Id::!(y in [])==> refParallelReduction(open'(0,y,t2a'),open'(0,y,t3a'));
                    Rule3Intro(t2a',t2b,t3a',t3b,[]);
                    assert refParallelReduction(t2,t3);
                }
        }
}

lemma Rule1Diamond(t:RefLambdaTerm, t1:RefLambdaTerm, t2:RefLambdaTerm)
    requires refRule1(t,t1)
    requires refRule1(t,t2)
    ensures exists t3:RefLambdaTerm :: refParallelReduction(t1,t3) && refParallelReduction(t2,t3)
{
    assert t==t1; 
    assert t==t2;
    var t3:=t;
    assert refParallelReduction(t1,t3) && refParallelReduction(t2,t3);
}

lemma ParDiamond(t:RefLambdaTerm, t1:RefLambdaTerm, t2:RefLambdaTerm)
    requires locallyClosed(t)
    requires refParallelReduction(t,t1)
    requires refParallelReduction(t,t2)
    ensures exists t3:RefLambdaTerm :: refParallelReduction(t1,t3) && refParallelReduction(t2,t3)
    decreases refLHeight(t), 2
{
    match t 
        case BoundVar(_)=>{assert false;}
        case FreeVar(_)=>{
            assert refRule1(t,t1);
            assert refRule1(t,t2);
            Rule1Diamond(t,t1,t2);
        }
        case App(ta,tb)=>
        {

            assert (refRule3(t,t1) && refRule3(t,t2)) || (refRule4(t,t1) && refRule3(t,t2)) || (refRule3(t,t1) && refRule4(t,t2)) || (refRule4(t,t1) && refRule4(t,t2));
            if (refRule4(t,t1) && refRule4(t,t2))
            {   
                var t1a:RefLambdaTerm,t1b:RefLambdaTerm:|t1==App(t1a,t1b);
                var t2a:RefLambdaTerm,t2b:RefLambdaTerm:|t2==App(t2a,t2b);
                assert refParallelReduction(ta,t1a);
                assert refParallelReduction(ta,t2a);
                ParDiamond(ta,t1a,t2a);
                var t3a:|refParallelReduction(t1a,t3a) && refParallelReduction(t2a,t3a);

                assert refParallelReduction(tb,t2b);
                assert refParallelReduction(tb,t1b);
                ParDiamond(tb,t1b,t2b);
                var t3b:|refParallelReduction(t1b,t3b) && refParallelReduction(t2b,t3b);

                var t3:=App(t3a,t3b);
                assert refRule4(t1,t3);
                assert refRule4(t2,t3);
                assert refParallelReduction(t1,t3) && refParallelReduction(t2,t3);
            }
            else 
            {
                assert (refRule3(t,t1) && refRule3(t,t2)) || (refRule4(t,t1) && refRule3(t,t2)) || (refRule3(t,t1) && refRule4(t,t2));
                if (refRule3(t,t1) && refRule4(t,t2))
                {
                    MixedRulesDiamond(t,t1,t2);
                }
                else 
                {
                     if (refRule4(t,t1) && refRule3(t,t2))
                     {
                        MixedRulesDiamond(t,t2,t1);
                     }
                     else 
                     {
                        assert refRule3(t,t1) && refRule3(t,t2);
                        Rule3Diamond(t,t1,t2);
                     }
                }
            }
        }
        case RefLambda(t')=>
        {
            assert refRule2(t,t1);
            assert refRule2(t,t2);
            LocalClosingEquivalence2(t);
            ParallelReductionPreservesClosure(t,t1);
            ParallelReductionPreservesClosure(t,t2);
            LocalClosingEquivalence1(t1);
            LocalClosingEquivalence1(t2);
            match t1 
                case RefLambda(t1')=>
                {
                    match t2 
                        case RefLambda(t2')=>
                        {
                            var L1:|allUnique(L1) && forall y:Id :: !(y in L1) ==> refParallelReduction(open'(0,y,t'),open'(0,y,t1'));
                            var L2:|allUnique(L2) && forall y:Id :: !(y in L2) ==> refParallelReduction(open'(0,y,t'),open'(0,y,t2'));

                            var L3:=reunion(reunion(L1,L2),reunion(freeVarsSeq(t1'),freeVarsSeq(t2')));

                            var x:Id:=addAnUniqueId(L3)[0];
                            NotInReunionSoNotInBoth(reunion(L1,L2),reunion(freeVarsSeq(t1'),freeVarsSeq(t2')),x);

                            NotInReunionSoNotInBoth(L1,L2,x);
                            assert !(x in L1) && !(x in L2);

                            NotInReunionSoNotInBoth(freeVarsSeq(t1'),freeVarsSeq(t2'),x);
                            assert !(x in freeVarsSeq(t1')) && !(x in freeVarsSeq(t2'));
                            
                            assert locallyClosed(RefLambda(t'));
                            OpeningIsClosed(t',x);

                            assert forall y:Id :: !(y in L1) ==> refParallelReduction(open'(0,y,t'),open'(0,y,t1'));
                            assert forall y:Id :: !(y in L2) ==> refParallelReduction(open'(0,y,t'),open'(0,y,t2'));
                            assert refParallelReduction(open'(0,x,t'),open'(0,x,t1'));
                            assert refParallelReduction(open'(0,x,t'),open'(0,x,t2'));
                            ParDiamond(open'(0,x,t'),open'(0,x,t1'),open'(0,x,t2'));
                            var t3':RefLambdaTerm :| refParallelReduction(open'(0,x,t1'),t3')
                                                && refParallelReduction(open'(0,x,t2'),t3');

                            ReductBodyIsClosed(t',t1',x);
                            ReductBodyIsClosed(t',t2',x);
                            var t3:RefLambdaTerm:=close(t3',x);
                            forall y:Id | !(y in [])
                                ensures refParallelReduction(open'(0,y,t1'),open'(0,y,t3)) &&
                                 refParallelReduction(open'(0,y,t2'),open'(0,y,t3))
                            {
                                Rule2Diamond(t1',t2',x,t3',y);
                            }
                            Rule2Intro(t1',t3,[]);
                            Rule2Intro(t2',t3,[]);
                            assert refParallelReduction(t1,RefLambda(t3)) && refParallelReduction(t2,RefLambda(t3));
                        }
                }
        }

}

lemma ReductBodyIsClosed(t:RefLambdaTerm, t1:RefLambdaTerm, x:Id)
    requires locallyClosed'(t,1)
    requires refParallelReduction(open'(0,x,t), open'(0,x,t1))
    ensures  locallyClosed'(t1,1)
{
    OpeningIsClosed'(t,x,0);
    ParReductionPreservesLocallyClosed(open'(0,x,t), open'(0,x,t1));
    BodyUp'(t1,x,0);
}
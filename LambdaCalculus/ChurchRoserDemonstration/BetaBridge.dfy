include "MainLemmas/LemmaA7.dfy"
include "ParallelReductionClosure.dfy"


lemma {:vcs_split_on_every_assert} BetaStepIsPar(t:LambdaTerm, choice:nat)
    requires 0 < numberOfPossibleReducations(t)
    requires choice < numberOfPossibleReducations(t)
    ensures parallelReduction(t, betaReductionStep(t, choice))
    decreases t
{
    if isCorrectForBetaReduction(t) {
        assert t.Application? && t.t1.Lambda?;
        var f := t.t1;
        var arg := t.t2;
        var x := f.x;
        var body := f.t;
        if choice == 0 {
            assert betaReductionStep(t, choice) == caSubstitution(body, x, arg);
            ParallelReductionIsReflexive(body);
            ParallelReductionIsReflexive(arg);
            EqualTermsAreAlphaEquilvalent(caSubstitution(body, x, arg), caSubstitution(body, x, arg));
            assert rule4(t, betaReductionStep(t, choice)) by {
                assert parallelReduction(body, body);
                assert parallelReduction(arg, arg);
                assert alphaEquivalence(betaReductionStep(t, choice), caSubstitution(body, x, arg));
            }
        } else {
            var n1 := numberOfPossibleReducations(f);
            if n1 >= choice {
                assert betaReductionStep(t, choice) == Application(betaReductionStep(f, choice-1), arg);
                var f' := betaReductionStep(f, choice-1);
                BetaStepIsPar(f, choice-1);
                ParallelReductionIsReflexive(arg);
                assert rule3(t, Application(f', arg)) by {
                    assert parallelReduction(f, f');
                    assert parallelReduction(arg, arg);
                }
            } else {
                assert betaReductionStep(t, choice) == Application(f, betaReductionStep(arg, choice-n1-1));
                var arg' := betaReductionStep(arg, choice-n1-1);
                BetaStepIsPar(arg, choice-n1-1);
                ParallelReductionIsReflexive(f);
                assert rule3(t, Application(f, arg')) by {
                    assert parallelReduction(f, f);
                    assert parallelReduction(arg, arg');
                }
            }
        }
    } else {
        match t {
            case Var(_) => { assert false; }
            case Lambda(x, body) => {
                assert betaReductionStep(t, choice) == Lambda(x, betaReductionStep(body, choice));
                var body' := betaReductionStep(body, choice);
                BetaStepIsPar(body, choice);
                EqualTermsAreAlphaEquilvalent(Lambda(x, body'), Lambda(x, body'));
                assert rule2(t, Lambda(x, body')) by {
                    assert parallelReduction(body, body');
                    assert alphaEquivalence(Lambda(x, body'), Lambda(x, body'));
                }
            }
            case Application(u, v) => {
                var n1 := numberOfPossibleReducations(u);
                if n1 > choice {
                    assert betaReductionStep(t, choice) == Application(betaReductionStep(u, choice), v);
                    var u' := betaReductionStep(u, choice);
                    BetaStepIsPar(u, choice);
                    ParallelReductionIsReflexive(v);
                    assert rule3(t, Application(u', v)) by {
                        assert parallelReduction(u, u');
                        assert parallelReduction(v, v);
                    }
                } else {
                    assert betaReductionStep(t, choice) == Application(u, betaReductionStep(v, choice-n1));
                    var v' := betaReductionStep(v, choice-n1);
                    BetaStepIsPar(v, choice-n1);
                    ParallelReductionIsReflexive(u);
                    assert rule3(t, Application(u, v')) by {
                        assert parallelReduction(u, u);
                        assert parallelReduction(v, v');
                    }
                }
            }
        }
    }
}

lemma BetaStepClosureIsPar(a:LambdaTerm, b:LambdaTerm)
    requires betaReductionClosure(a, b)
    ensures parallelReduction(a, b)
{
    var choice:nat :| choice < numberOfPossibleReducations(a) && betaReductionStep(a, choice) == b;
    BetaStepIsPar(a, choice);
}

lemma BetaStarToParStarN(a:LambdaTerm, b:LambdaTerm, n:nat)
    requires betaReducationInNSteps(a, b, n)
    ensures parallelReductionClosure(a, b)
    decreases n
{
    if n == 0 {
        assert betaReducationInNSteps(a, b, 0);    
        assert alphaEquivalence(a, b);
        assert parallelReductionInNSteps(a, b, 0);  
    } else {
        var s, a' :| alphaEquivalence(a, s) && betaReductionClosure(s, a') && betaReducationInNSteps(a', b, n-1);
        assert parallelReduction(a, s);
        BetaStepClosureIsPar(s, a');
        BetaStarToParStarN(a', b, n-1);
        ParClosurePrepend(s, a', b);
        ParClosurePrepend(a, s, b);
    }
}


lemma BetaStarToParStar(a:LambdaTerm, b:LambdaTerm)
    requires betaReducationsClosure(a, b)
    ensures parallelReductionClosure(a, b)
{
    var n:nat :| betaReducationInNSteps(a, b, n);
    BetaStarToParStarN(a, b, n);
}


lemma BetaInNStepsLeftAlpha(u:LambdaTerm, t1:LambdaTerm, t2:LambdaTerm, n:nat)
    requires alphaEquivalence(u, t1)
    requires betaReducationInNSteps(t1, t2, n)
    ensures  betaReducationInNSteps(u, t2, n)
    decreases n
{
    if n == 0 {
        AlphaEquivTransitive(u, t1, t2);
    } else {
        var s, t' :| alphaEquivalence(t1, s) && betaReductionClosure(s, t') && betaReducationInNSteps(t', t2, n-1);
        AlphaEquivTransitive(u, t1, s);
        assert alphaEquivalence(u, s) && betaReductionClosure(s, t') && betaReducationInNSteps(t', t2, n-1);
    }
}

lemma BetaInNStepsConcat(a:LambdaTerm, b:LambdaTerm, c:LambdaTerm, n:nat, m:nat)
    requires betaReducationInNSteps(a, b, n)
    requires betaReducationInNSteps(b, c, m)
    ensures  betaReducationInNSteps(a, c, n+m)
    decreases n
{
    if n == 0 {
        BetaInNStepsLeftAlpha(a, b, c, m);
    } else {
        var s, a' :| alphaEquivalence(a, s) && betaReductionClosure(s, a') && betaReducationInNSteps(a', b, n-1);
        BetaInNStepsConcat(a', b, c, n-1, m);
        assert alphaEquivalence(a, s) && betaReductionClosure(s, a') && betaReducationInNSteps(a', c, (n-1)+m);
        assert betaReducationInNSteps(a, c, n+m);
    }
}

lemma BetaStarLeftAlpha(u:LambdaTerm, a:LambdaTerm, b:LambdaTerm)
    requires alphaEquivalence(u, a)
    requires betaReducationsClosure(a, b)
    ensures  betaReducationsClosure(u, b)
{
    var n:nat :| betaReducationInNSteps(a, b, n);
    BetaInNStepsLeftAlpha(u, a, b, n);
}


lemma BetaStarTrans(a:LambdaTerm, b:LambdaTerm, c:LambdaTerm)
    requires betaReducationsClosure(a, b)
    requires betaReducationsClosure(b, c)
    ensures  betaReducationsClosure(a, c)
{
    var n1:nat:|betaReducationInNSteps(a,b,n1);
    var n2:nat:|betaReducationInNSteps(b,c,n2);
    BetaInNStepsConcat(a,b,c,n1,n2);
    assert betaReducationInNSteps(a,c,n1+n2);

}

lemma BetaStarAlphaRight(a:LambdaTerm, b:LambdaTerm, b':LambdaTerm)
    requires betaReducationsClosure(a, b)
    requires alphaEquivalence(b, b')
    ensures  exists b'':LambdaTerm :: betaReducationsClosure(a, b'') && alphaEquivalence(b'', b')
{
    assert betaReducationsClosure(a, b) && alphaEquivalence(b, b');
}

lemma LambdaCongStep(x:Id, M:LambdaTerm, M':LambdaTerm)
    requires betaReductionClosure(M, M')
    ensures  betaReductionClosure(Lambda(x, M), Lambda(x, M'))
{
    var c:nat :| c < numberOfPossibleReducations(M) && betaReductionStep(M, c) == M';
    assert numberOfPossibleReducations(Lambda(x, M)) == numberOfPossibleReducations(M);
    assert !isCorrectForBetaReduction(Lambda(x, M));
    assert betaReductionStep(Lambda(x, M), c) == Lambda(x, betaReductionStep(M, c));
    assert betaReductionStep(Lambda(x, M), c) == Lambda(x, M');
}

lemma LambdaCongInN(x:Id, M:LambdaTerm, M':LambdaTerm, n:nat)
    requires betaReducationInNSteps(M, M', n)
    ensures  betaReducationInNSteps(Lambda(x, M), Lambda(x, M'), n)
    decreases n
{
    if n == 0 {
        AlphaCongruenceLambda(x, M, M');
    } else {
        var s, M1 :| alphaEquivalence(M, s) && betaReductionClosure(s, M1) && betaReducationInNSteps(M1, M', n-1);
        AlphaCongruenceLambda(x, M, s);
        LambdaCongStep(x, s, M1);
        LambdaCongInN(x, M1, M', n-1);
        assert alphaEquivalence(Lambda(x,M), Lambda(x,s))
            && betaReductionClosure(Lambda(x,s), Lambda(x,M1))
            && betaReducationInNSteps(Lambda(x,M1), Lambda(x,M'), n-1);
    }
}

lemma LambdaCongBetaStar(x:Id, M:LambdaTerm, M':LambdaTerm)
    requires betaReducationsClosure(M, M')
    ensures  betaReducationsClosure(Lambda(x, M), Lambda(x, M'))
{
    var n:nat :| betaReducationInNSteps(M, M', n);
    LambdaCongInN(x, M, M', n);
}

lemma AppCongLeftStep(P:LambdaTerm, P':LambdaTerm, Q:LambdaTerm)
    requires betaReductionClosure(P, P')
    ensures  betaReductionClosure(Application(P, Q), Application(P', Q))
{
    var c:nat :| c < numberOfPossibleReducations(P) && betaReductionStep(P, c) == P';
    var t := Application(P, Q);
    var n1 := numberOfPossibleReducations(P);
    if isCorrectForBetaReduction(t) {
        assert numberOfPossibleReducations(t) == 1 + n1 + numberOfPossibleReducations(Q);
        var choice := c + 1;
        assert choice < numberOfPossibleReducations(t);
        assert choice != 0 && n1 >= choice;
        assert betaReductionStep(t, choice) == Application(betaReductionStep(P, choice-1), Q);
        assert betaReductionStep(t, choice) == Application(P', Q);
    } else {
        assert numberOfPossibleReducations(t) == n1 + numberOfPossibleReducations(Q);
        var choice := c;
        assert n1 > choice;
        assert betaReductionStep(t, choice) == Application(betaReductionStep(P, choice), Q);
        assert betaReductionStep(t, choice) == Application(P', Q);
    }
}
lemma AppCongRightStep(P:LambdaTerm, Q:LambdaTerm, Q':LambdaTerm)
    requires betaReductionClosure(Q, Q')
    ensures  betaReductionClosure(Application(P, Q), Application(P, Q'))
{
    var c:nat :| c < numberOfPossibleReducations(Q) && betaReductionStep(Q, c) == Q';
    var t := Application(P, Q);
    var n1 := numberOfPossibleReducations(P);
    if isCorrectForBetaReduction(t) {
        assert numberOfPossibleReducations(t) == 1 + n1 + numberOfPossibleReducations(Q);
        var choice := 1 + n1 + c;
        assert choice < numberOfPossibleReducations(t);
        assert choice != 0 && !(n1 >= choice);
        assert choice - n1 - 1 == c;
        assert betaReductionStep(t, choice) == Application(P, betaReductionStep(Q, choice-n1-1));
        assert betaReductionStep(t, choice) == Application(P, Q');
    } else {
        assert numberOfPossibleReducations(t) == n1 + numberOfPossibleReducations(Q);
        var choice := n1 + c;
        assert !(n1 > choice);
        assert choice - n1 == c;
        assert betaReductionStep(t, choice) == Application(P, betaReductionStep(Q, choice-n1));
        assert betaReductionStep(t, choice) == Application(P, Q');
    }
}

lemma AppCongLeftInN(P:LambdaTerm, P':LambdaTerm, Q:LambdaTerm, n:nat)
    requires betaReducationInNSteps(P, P', n)
    ensures  betaReducationInNSteps(Application(P, Q), Application(P', Q), n)
    decreases n
{
    if n == 0 {
        EqualTermsAreAlphaEquilvalent(Q, Q);
        ApplicationEquivalence(P, P', Q, Q);
    } else {
        var s, P1 :| alphaEquivalence(P, s) && betaReductionClosure(s, P1) && betaReducationInNSteps(P1, P', n-1);
        EqualTermsAreAlphaEquilvalent(Q, Q);
        ApplicationEquivalence(P, s, Q, Q);
        AppCongLeftStep(s, P1, Q);
        AppCongLeftInN(P1, P', Q, n-1);
        assert alphaEquivalence(Application(P,Q), Application(s,Q))
            && betaReductionClosure(Application(s,Q), Application(P1,Q))
            && betaReducationInNSteps(Application(P1,Q), Application(P',Q), n-1);
    }
}

lemma AppCongLeftBetaStar(P:LambdaTerm, P':LambdaTerm, Q:LambdaTerm)
    requires betaReducationsClosure(P, P')
    ensures  betaReducationsClosure(Application(P, Q), Application(P', Q))
{
    var n:nat :| betaReducationInNSteps(P, P', n);
    AppCongLeftInN(P, P', Q, n);
}

lemma AppCongRightInN(P:LambdaTerm, Q:LambdaTerm, Q':LambdaTerm, n:nat)
    requires betaReducationInNSteps(Q, Q', n)
    ensures  betaReducationInNSteps(Application(P, Q), Application(P, Q'), n)
    decreases n
{
    if n == 0 {
        EqualTermsAreAlphaEquilvalent(P, P);
        ApplicationEquivalence(P, P, Q, Q');
    } else {
        var s, Q1 :| alphaEquivalence(Q, s) && betaReductionClosure(s, Q1) && betaReducationInNSteps(Q1, Q', n-1);
        EqualTermsAreAlphaEquilvalent(P, P);
        ApplicationEquivalence(P, P, Q, s);
        AppCongRightStep(P, s, Q1);
        AppCongRightInN(P, Q1, Q', n-1);
        assert alphaEquivalence(Application(P,Q), Application(P,s))
            && betaReductionClosure(Application(P,s), Application(P,Q1))
            && betaReducationInNSteps(Application(P,Q1), Application(P,Q'), n-1);
    }
}

lemma AppCongRightBetaStar(P:LambdaTerm, Q:LambdaTerm, Q':LambdaTerm)
    requires betaReducationsClosure(Q, Q')
    ensures  betaReducationsClosure(Application(P, Q), Application(P, Q'))
{
    var n:nat :| betaReducationInNSteps(Q, Q', n);
    AppCongRightInN(P, Q, Q', n);
}

lemma StepIsBetaStar(a:LambdaTerm, b:LambdaTerm)
    requires betaReductionClosure(a, b)
    ensures  betaReducationsClosure(a, b)
{
    EqualTermsAreAlphaEquilvalent(a, a);
    EqualTermsAreAlphaEquilvalent(b, b);
    assert betaReducationInNSteps(b, b, 0);
    assert betaReducationInNSteps(a, b, 1);
}

lemma RootBetaStep(x:Id, M:LambdaTerm, Q:LambdaTerm)
    ensures betaReductionClosure(Application(Lambda(x,M), Q), caSubstitution(M, x, Q))
{
    var t := Application(Lambda(x,M), Q);
    assert isCorrectForBetaReduction(t);
    assert numberOfPossibleReducations(t) >= 1;
    assert betaReductionStep(t, 0) == betaReduction(t) == caSubstitution(M, x, Q);
}

lemma ParStepIsBetaStar(a:LambdaTerm, b:LambdaTerm)
    requires parallelReduction(a, b)
    ensures  exists b':LambdaTerm :: betaReducationsClosure(a, b') && alphaEquivalence(b', b)
    decreases lHeight(a)
{
    ParallelReductionIsBasedOnFourRules(a, b);
    if alphaEquivalence(a, b) {
        // 0 steps: b' = a.
        EqualTermsAreAlphaEquilvalent(a, a);
        assert betaReducationInNSteps(a, a, 0);
        assert betaReducationsClosure(a, a) && alphaEquivalence(a, b);
        return;
    }
    match a {
        case Var(z) => {
            assert false;   
        }
        case Lambda(x, M) => {
            LambdaParallelLemma(M, b, x);
            var M' :| parallelReduction(M, M') && alphaEquivalence(Lambda(x, M'), b);
            ParStepIsBetaStar(M, M');
            var M'' :| betaReducationsClosure(M, M'') && alphaEquivalence(M'', M');
            LambdaCongBetaStar(x, M, M'');
            AlphaCongruenceLambda(x, M'', M');
            AlphaEquivTransitive(Lambda(x,M''), Lambda(x,M'), b);
            assert betaReducationsClosure(a, Lambda(x,M'')) && alphaEquivalence(Lambda(x,M''), b);
        }
        case Application(P, Q) => {
            AlphaParallelLemma(P, Q, b);
            if (exists Pp:LambdaTerm, Qp:LambdaTerm ::
                    parallelReduction(P,Pp) && parallelReduction(Q,Qp) && alphaEquivalence(Application(Pp,Qp), b)) {
                var Pp, Qp :| parallelReduction(P,Pp) && parallelReduction(Q,Qp) && alphaEquivalence(Application(Pp,Qp), b);
                ParStepIsBetaStar(P, Pp);
                var P'' :| betaReducationsClosure(P, P'') && alphaEquivalence(P'', Pp);
                ParStepIsBetaStar(Q, Qp);
                var Q'' :| betaReducationsClosure(Q, Q'') && alphaEquivalence(Q'', Qp);
                AppCongLeftBetaStar(P, P'', Q);
                AppCongRightBetaStar(P'', Q, Q'');
                BetaStarTrans(Application(P,Q), Application(P'',Q), Application(P'',Q''));
                ApplicationEquivalence(P'', Pp, Q'', Qp);
                AlphaEquivTransitive(Application(P'',Q''), Application(Pp,Qp), b);
                assert betaReducationsClosure(a, Application(P'',Q'')) && alphaEquivalence(Application(P'',Q''), b);
            } else {
                assert P.Lambda?;
                var x := P.x;
                var Pb := P.t;
                var P', Q' :| parallelReduction(Pb, P') && parallelReduction(Q, Q')
                            && alphaEquivalence(b, caSubstitution(P', x, Q'));
                ParStepIsBetaStar(Pb, P');
                var P'' :| betaReducationsClosure(Pb, P'') && alphaEquivalence(P'', P');
                ParStepIsBetaStar(Q, Q');
                var Q'' :| betaReducationsClosure(Q, Q'') && alphaEquivalence(Q'', Q');
                LambdaCongBetaStar(x, Pb, P'');
                AppCongLeftBetaStar(Lambda(x,Pb), Lambda(x,P''), Q);
                AppCongRightBetaStar(Lambda(x,P''), Q, Q'');
                BetaStarTrans(Application(Lambda(x,Pb),Q), Application(Lambda(x,P''),Q), Application(Lambda(x,P''),Q''));
                RootBetaStep(x, P'', Q'');
                StepIsBetaStar(Application(Lambda(x,P''),Q''), caSubstitution(P'', x, Q''));
                BetaStarTrans(Application(Lambda(x,Pb),Q), Application(Lambda(x,P''),Q''), caSubstitution(P'', x, Q''));
                CaSubstEquivalence(P'', Q'', P', Q', x);
                AlphaEquivSymmetric(b, caSubstitution(P', x, Q'));
                AlphaEquivTransitive(caSubstitution(P'', x, Q''), caSubstitution(P', x, Q'), b);
                assert betaReducationsClosure(a, caSubstitution(P'', x, Q'')) && alphaEquivalence(caSubstitution(P'', x, Q''), b);
            }
        }
    }
}

lemma ParStarToBetaStarN(a:LambdaTerm, b:LambdaTerm, n:nat)
    requires parallelReductionInNSteps(a, b, n)
    ensures  exists b':LambdaTerm :: betaReducationsClosure(a, b') && alphaEquivalence(b', b)
    decreases n
{
    if n == 0 {
        EqualTermsAreAlphaEquilvalent(a, a);
        assert betaReducationInNSteps(a, a, 0);
        assert betaReducationsClosure(a, a) && alphaEquivalence(a, b);
    } else {
        var a1 :| parallelReduction(a, a1) && parallelReductionInNSteps(a1, b, n-1);
        ParStepIsBetaStar(a, a1);
        var a1' :| betaReducationsClosure(a, a1') && alphaEquivalence(a1', a1);
        ParStarToBetaStarN(a1, b, n-1);
        var b'' :| betaReducationsClosure(a1, b'') && alphaEquivalence(b'', b);
        BetaStarLeftAlpha(a1', a1, b'');
        BetaStarTrans(a, a1', b'');
        assert betaReducationsClosure(a, b'') && alphaEquivalence(b'', b);
    }
}

lemma ParStarToBetaStar(a:LambdaTerm, b:LambdaTerm)
    requires parallelReductionClosure(a, b)
    ensures  exists b':LambdaTerm :: betaReducationsClosure(a, b') && alphaEquivalence(b', b)
{
    var n:nat :| parallelReductionInNSteps(a, b, n);
    ParStarToBetaStarN(a, b, n);
}

lemma ChurchRosser(a:LambdaTerm, b:LambdaTerm, c:LambdaTerm)
    requires betaReducationsClosure(a, b)
    requires betaReducationsClosure(a, c)
    ensures exists d1:LambdaTerm, d2:LambdaTerm ::
        betaReducationsClosure(b, d1) && betaReducationsClosure(c, d2) && alphaEquivalence(d1, d2)
{
    BetaStarToParStar(a, b);
    BetaStarToParStar(a, c);
    ParallelClosureHasDiamond(a, b, c);
    var d :| parallelReductionClosure(b, d) && parallelReductionClosure(c, d);
    ParStarToBetaStar(b, d);
    var d1 :| betaReducationsClosure(b, d1) && alphaEquivalence(d1, d);
    ParStarToBetaStar(c, d);
    var d2 :LambdaTerm:| betaReducationsClosure(c, d2) && alphaEquivalence(d2, d);
    AlphaEquivSymmetric(d2, d);
    AlphaEquivTransitive(d1, d, d2);
}

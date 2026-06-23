include "../MainLemmas/LemmaA2.dfy"

lemma ParallelReductionAlphaInvariance(t1: LambdaTerm, t2: LambdaTerm, t1': LambdaTerm, t2': LambdaTerm)
    requires parallelReduction(t1, t2)
    requires alphaEquivalence(t1, t1')
    requires alphaEquivalence(t2, t2')
    ensures parallelReduction(t1', t2')
    decreases lHeight(t1), 0
{
    if alphaEquivalence(t1, t2) {
        AlphaEquivSymmetric(t1, t1');
        AlphaEquivTransitive(t1', t1, t2);
        AlphaEquivTransitive(t1', t2, t2');
        return;
    }
    match t1 {
        case Var(z) => {
            assert false;
        }
        case Lambda(x, body1) => {
            var r :| parallelReduction(body1, r) && alphaEquivalence(Lambda(x, r), t2);
            NonLambdaAlphaEquivalence(t1, t1');
            match t1' {
                case Lambda(x', body1') => {
                    ParRedAlphaUnderBinder(x, body1, r, x', body1');
                    var RR :| parallelReduction(body1', RR) && alphaEquivalence(Lambda(x', RR), Lambda(x, r));
                    AlphaEquivTransitive(Lambda(x', RR), Lambda(x, r), t2);
                    AlphaEquivTransitive(Lambda(x', RR), t2, t2');
                    ParRedLambdaIntro(x', body1', RR, t2');
                }
                case _ => {}
            }
        }
        case Application(t1a, t1b) => {
            NonApplicationAlphaEquivalence(t1, t1');
            match t1' {
                case Application(t1a', t1b') => {
                    ApplicationEquivalenceDown(t1a, t1b, t1a', t1b');
                    if t2.Application? && parallelReduction(t1a, t2.t1) && parallelReduction(t1b, t2.t2) {
                        NonApplicationAlphaEquivalence(t2, t2');
                        match t2' {
                            case Application(t2a', t2b') => {
                                ApplicationEquivalenceDown(t2.t1, t2.t2, t2a', t2b');
                                ParallelReductionAlphaInvariance(t1a, t2.t1, t1a', t2a');
                                ParallelReductionAlphaInvariance(t1b, t2.t2, t1b', t2b');
                                assert parallelReduction(t1a', t2a') && parallelReduction(t1b', t2b');
                            }
                            case _ => {}
                        }
                    } else {
                        match t1a {
                            case Lambda(x, M) => {
                                var M', N' :| parallelReduction(M, M') && parallelReduction(t1b, N')
                                              && alphaEquivalence(t2, caSubstitution(M', x, N'));
                                NonLambdaAlphaEquivalence(t1a, t1a');
                                match t1a' {
                                    case Lambda(x', body') => {
                                        ParRedAlphaUnderBinder(x, M, M', x', body');
                                        var M'' :| parallelReduction(body', M'')
                                                   && alphaEquivalence(Lambda(x', M''), Lambda(x, M'));
                                        EqualTermsAreAlphaEquilvalent(N', N');
                                        ParallelReductionAlphaInvariance(t1b, N', t1b', N');
                                        AlphaEquivSymmetric(Lambda(x', M''), Lambda(x, M'));
                                        SubstRespectsBinderAlpha(x, M', x', M'', N');
                                        AlphaEquivSymmetric(t2, t2');
                                        AlphaEquivTransitive(t2', t2, caSubstitution(M', x, N'));
                                        AlphaEquivTransitive(t2', caSubstitution(M', x, N'), caSubstitution(M'', x', N'));
                                        ParRedBetaIntro(x', body', t1b', M'', N', t2');
                                    }
                                    case _ => {}
                                }
                            }
                            case _ => {}
                        }
                    }
                }
                case _ => {}
            }
        }
    }
}
lemma {:vcs_split_on_every_assert} ParRedRename(M:LambdaTerm, M':LambdaTerm, a:Id, b:Id)
    requires parallelReduction(M, M')
    ensures parallelReduction(caSubstitution(M, a, Var(b)), caSubstitution(M', a, Var(b)))
    decreases lHeight(M), 1
{
    var Mca := caSubstitution(M, a, Var(b));
    var M'ca := caSubstitution(M', a, Var(b));
    if alphaEquivalence(M, M') {
        EqualTermsAreAlphaEquilvalent(Var(b), Var(b));
        CaSubstEquivalence(M, Var(b), M', Var(b), a);
        return;
    }
    match M {
        case Var(z) => { assert false; }
        case Lambda(z, body) => {
            var s :| parallelReduction(body, s) && alphaEquivalence(Lambda(z, s), M');
            var S := addition(a, addition(b, reunion(vars(M), reunion(vars(M'), vars(s)))));
            reunionIncludesBothSets(vars(M'), vars(s));
            reunionIncludesBothSets(vars(M), reunion(vars(M'), vars(s)));
            var zf := addAnUniqueId(S)[0];
            assert !(zf in S);
            assert zf != a && zf != b;
            varsOfALambdaIncludesVarsofASubLambda(M);
            assert !(zf in vars(M)) && !(zf in vars(M')) && !(zf in vars(s));
            assert !(zf in vars(body));

            var body_alt := substitution(body, z, Var(zf));
            var s_alt := substitution(s, z, Var(zf));

            ParRedRename(body, s, z, zf);
            CaSubstIsNaiveWhenFresh(body, z, zf);
            CaSubstIsNaiveWhenFresh(s, z, zf);
            assert parallelReduction(body_alt, s_alt);

            subsitutionOfVarDoesNotChangeHeightFORVARIABLES(body, z, Var(zf));
            ParRedRename(body_alt, s_alt, a, b);
            var PbA := caSubstitution(body_alt, a, Var(b));
            var rr := caSubstitution(s_alt, a, Var(b));
            assert parallelReduction(PbA, rr);

            SubstAlphaEquivalence(body, z, zf);
            EqualTermsAreAlphaEquilvalent(Var(b), Var(b));
            CaSubstEquivalence(M, Var(b), Lambda(zf, body_alt), Var(b), a);
            SubstPushesIntoSafeLambda(zf, body_alt, a, Var(b));
            AlphaEquivTransitive(Mca, caSubstitution(Lambda(zf, body_alt), a, Var(b)), Lambda(zf, PbA));

            SubstAlphaEquivalence(s, z, zf);
            AlphaEquivTransitive(Lambda(zf, s_alt), Lambda(z, s), M');
            CaSubstEquivalence(Lambda(zf, s_alt), Var(b), M', Var(b), a);
            SubstPushesIntoSafeLambda(zf, s_alt, a, Var(b));
            AlphaEquivSymmetric(caSubstitution(Lambda(zf, s_alt), a, Var(b)), Lambda(zf, rr));
            AlphaEquivTransitive(Lambda(zf, rr), caSubstitution(Lambda(zf, s_alt), a, Var(b)), M'ca);

            ParRedLambdaIntro(zf, PbA, rr, M'ca);
            AlphaEquivSymmetric(Mca, Lambda(zf, PbA));
            EqualTermsAreAlphaEquilvalent(M'ca, M'ca);
            CaSubsitutionOfVarDoesNotChangeHeightFORVARIABLES(body_alt, a, Var(b));
            ParallelReductionAlphaInvariance(Lambda(zf, PbA), M'ca, Mca, M'ca);
        }
        case Application(P, Q) => {
            if M'.Application? && parallelReduction(P, M'.t1) && parallelReduction(Q, M'.t2) {
                var Pp := M'.t1;
                var Qp := M'.t2;
                SubstDistributesOverApp(P, Q, a, Var(b));
                SubstDistributesOverApp(Pp, Qp, a, Var(b));
                ParRedRename(P, Pp, a, b);
                ParRedRename(Q, Qp, a, b);
                var PA := caSubstitution(P, a, Var(b));
                var QA := caSubstitution(Q, a, Var(b));
                var PpA := caSubstitution(Pp, a, Var(b));
                var QpA := caSubstitution(Qp, a, Var(b));
                ParRedCongIntro(PA, QA, PpA, QpA);
                AlphaEquivSymmetric(Mca, Application(PA, QA));
                AlphaEquivSymmetric(M'ca, Application(PpA, QpA));
                CaSubsitutionOfVarDoesNotChangeHeightFORVARIABLES(P, a, Var(b));
                CaSubsitutionOfVarDoesNotChangeHeightFORVARIABLES(Q, a, Var(b));
                ParallelReductionAlphaInvariance(Application(PA, QA), Application(PpA, QpA), Mca, M'ca);
            } else {
                match P {
                    case Lambda(z, Pb) => {
                        var Pb', Q'' :| parallelReduction(Pb, Pb') && parallelReduction(Q, Q'')
                                        && alphaEquivalence(M', caSubstitution(Pb', z, Q''));
                        var S := addition(a, addition(b, reunion(vars(M), reunion(vars(M'),
                                    reunion(vars(Pb'), vars(Q''))))));
                        reunionIncludesBothSets(vars(Pb'), vars(Q''));
                        reunionIncludesBothSets(vars(M'), reunion(vars(Pb'), vars(Q'')));
                        reunionIncludesBothSets(vars(M), reunion(vars(M'), reunion(vars(Pb'), vars(Q''))));
                        var zf := addAnUniqueId(S)[0];
                        assert !(zf in S);
                        assert zf != a && zf != b;
                        varsOfALambdaIncludesVarsofASubLambda(M);
                        varsOfALambdaIncludesVarsofASubLambda(P);
                        assert !(zf in vars(M)) && !(zf in vars(M')) && !(zf in vars(Pb')) && !(zf in vars(Q''));
                        assert !(zf in vars(P));
                        assert !(zf in vars(Pb)) && !(zf in vars(Q));

                        var Pb_alt := substitution(Pb, z, Var(zf));
                        var Pb'_alt := substitution(Pb', z, Var(zf));

                        assert parallelReduction(Pb, Pb');
                        assert lHeight(Pb) < lHeight(M);
                        ParRedRename(Pb, Pb', z, zf);
                        CaSubstIsNaiveWhenFresh(Pb, z, zf);
                        CaSubstIsNaiveWhenFresh(Pb', z, zf);
                        assert parallelReduction(Pb_alt, Pb'_alt);

                        subsitutionOfVarDoesNotChangeHeightFORVARIABLES(Pb, z, Var(zf));
                        var PbA := caSubstitution(Pb_alt, a, Var(b));
                        var QA := caSubstitution(Q, a, Var(b));
                        var P2 := caSubstitution(Pb'_alt, a, Var(b));
                        var N2 := caSubstitution(Q'', a, Var(b));

                        ParRedRename(Pb_alt, Pb'_alt, a, b);
                        ParRedRename(Q, Q'', a, b);
                        assert parallelReduction(PbA, P2);
                        assert parallelReduction(QA, N2);

                        var LHSapp := Application(Lambda(zf, PbA), QA);

                        SubstAlphaEquivalence(Pb, z, zf);
                        EqualTermsAreAlphaEquilvalent(Q, Q);
                        ApplicationEquivalence(Lambda(z, Pb), Lambda(zf, Pb_alt), Q, Q);
                        EqualTermsAreAlphaEquilvalent(Var(b), Var(b));
                        CaSubstEquivalence(M, Var(b), Application(Lambda(zf, Pb_alt), Q), Var(b), a);
                        SubstDistributesOverApp(Lambda(zf, Pb_alt), Q, a, Var(b));
                        SubstPushesIntoSafeLambda(zf, Pb_alt, a, Var(b));
                        EqualTermsAreAlphaEquilvalent(QA, QA);
                        ApplicationEquivalence(caSubstitution(Lambda(zf, Pb_alt), a, Var(b)), Lambda(zf, PbA), QA, QA);
                        AlphaEquivTransitive(Mca,
                                             caSubstitution(Application(Lambda(zf, Pb_alt), Q), a, Var(b)),
                                             Application(caSubstitution(Lambda(zf, Pb_alt), a, Var(b)), QA));
                        AlphaEquivTransitive(Mca,
                                             Application(caSubstitution(Lambda(zf, Pb_alt), a, Var(b)), QA),
                                             LHSapp);

                        SubstAlphaEquivalence(Pb', z, zf);
                        SubstRespectsBinderAlpha(z, Pb', zf, Pb'_alt, Q'');
                        AlphaEquivTransitive(M', caSubstitution(Pb', z, Q''), caSubstitution(Pb'_alt, zf, Q''));
                        EqualTermsAreAlphaEquilvalent(Var(b), Var(b));
                        CaSubstEquivalence(M', Var(b), caSubstitution(Pb'_alt, zf, Q''), Var(b), a);
                        SubstitutionLemma(Pb'_alt, Q'', Var(b), zf, a);
                        AlphaEquivTransitive(M'ca,
                                             caSubstitution(caSubstitution(Pb'_alt, zf, Q''), a, Var(b)),
                                             caSubstitution(P2, zf, N2));

                        ParRedBetaIntro(zf, PbA, QA, P2, N2, M'ca);
                        AlphaEquivSymmetric(Mca, LHSapp);
                        EqualTermsAreAlphaEquilvalent(M'ca, M'ca);
                        CaSubsitutionOfVarDoesNotChangeHeightFORVARIABLES(Pb_alt, a, Var(b));
                        CaSubsitutionOfVarDoesNotChangeHeightFORVARIABLES(Q, a, Var(b));
                        ParallelReductionAlphaInvariance(LHSapp, M'ca, Mca, M'ca);
                    }
                    case _ => { assert false; }
                }
            }
        }
    }
}

lemma {:vcs_split_on_every_assert} ParRedAlphaUnderBinder(x:Id, B:LambdaTerm, R:LambdaTerm, x2:Id, B2arg:LambdaTerm)
    requires parallelReduction(B, R)
    requires alphaEquivalence(Lambda(x, B), Lambda(x2, B2arg))
    ensures exists RR :: parallelReduction(B2arg, RR) && alphaEquivalence(Lambda(x2, RR), Lambda(x, R))
    decreases lHeight(B), 2
{
    if x == x2 {
        StripSameBinder(x, B, B2arg);
        EqualTermsAreAlphaEquilvalent(R, R);
        ParallelReductionAlphaInvariance(B, R, B2arg, R);
        EqualTermsAreAlphaEquilvalent(Lambda(x2, R), Lambda(x, R));
        assert parallelReduction(B2arg, R) && alphaEquivalence(Lambda(x2, R), Lambda(x, R));
    } else {
        BinderRenameNotFree(x, B, x2, B2arg);
        ParRedPreservesNonFree(B, R, x2);
        AvoidVarInTerm(B, x2);
        var Bc :| alphaEquivalence(B, Bc) && !(x2 in vars(Bc));
        AvoidVarInTerm(R, x2);
        var Rc :| alphaEquivalence(R, Rc) && !(x2 in vars(Rc));

        AlphaSameHeight(B, Bc);
        ParallelReductionAlphaInvariance(B, R, Bc, Rc);

        AlphaEquivSymmetric(B, Bc);
        AlphaCongruenceLambda(x, Bc, B);
        AlphaEquivTransitive(Lambda(x, Bc), Lambda(x, B), Lambda(x2, B2arg));

        ParRedRename(Bc, Rc, x, x2);
        var BcS := caSubstitution(Bc, x, Var(x2));
        var RR := caSubstitution(Rc, x, Var(x2));
        assert parallelReduction(BcS, RR);

        CaSubstIsNaiveWhenFresh(Bc, x, x2);
        SubstAlphaEquivalence(Bc, x, x2);
        AlphaEquivSymmetric(Lambda(x, Bc), Lambda(x2, B2arg));
        AlphaEquivTransitive(Lambda(x2, B2arg), Lambda(x, Bc), Lambda(x2, BcS));
        StripSameBinder(x2, B2arg, BcS);
        AlphaEquivSymmetric(B2arg, BcS);

        CaSubsitutionOfVarDoesNotChangeHeightFORVARIABLES(Bc, x, Var(x2));
        EqualTermsAreAlphaEquilvalent(RR, RR);
        ParallelReductionAlphaInvariance(BcS, RR, B2arg, RR);

        CaSubstIsNaiveWhenFresh(Rc, x, x2);
        SubstAlphaEquivalence(Rc, x, x2);
        AlphaEquivSymmetric(R, Rc);
        AlphaCongruenceLambda(x, Rc, R);
        AlphaEquivSymmetric(Lambda(x, Rc), Lambda(x2, RR));
        AlphaEquivTransitive(Lambda(x2, RR), Lambda(x, Rc), Lambda(x, R));

        assert parallelReduction(B2arg, RR) && alphaEquivalence(Lambda(x2, RR), Lambda(x, R));
    }
}




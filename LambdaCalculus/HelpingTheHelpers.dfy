// include "ParallelReduction.dfy"
// include "SubstitutionsAndSets.dfy"
// include "LemmaA3.dfy"

// lemma StripOuterBinder(t1:LambdaTerm, t2:LambdaTerm, w:Id, id1:seq<Id>, id2:seq<Id>)
//     requires alphaEquivalence'(t1, t2, [w]+id1, [w]+id2)
//     ensures alphaEquivalence'(t1, t2, id1, id2)
//     decreases minim(lHeight(t1), lHeight(t2))
//                 {
//     match t1 {
//         case Var(x) => {
//             var z :| t2 == Var(z);
//             findId_prepend(id1, x, w);
//             findId_prepend(id2, z, w);
//         }
//         case Lambda(x, t1b) => {
//             var z, t2b :| t2 == Lambda(z, t2b);
//             assert ([w]+id1)+[x] == [w]+(id1+[x]);
//             assert ([w]+id2)+[z] == [w]+(id2+[z]);
//             StripOuterBinder(t1b, t2b, w, id1+[x], id2+[z]);
//         }
//         case Application(t1a, t1b) => {
//             var t2a, t2b :| t2 == Application(t2a, t2b);
//             StripOuterBinder(t1a, t2a, w, id1, id2);
//             StripOuterBinder(t1b, t2b, w, id1, id2);
//         }
//     }
// }

// lemma StripSameBinder(w:Id, a:LambdaTerm, b:LambdaTerm)
//     requires alphaEquivalence(Lambda(w,a), Lambda(w,b))
//     ensures alphaEquivalence(a, b)
// {
//     assert []+[w] == [w];
//     assert [w] == [w]+[];
//     StripOuterBinder(a, b, w, [], []);
// }

// lemma FreeSubsetVars(t:LambdaTerm)
//     ensures forall i:Id :: i in free(t) ==> i in vars(t)
// {
//     match t {
//         case Var(_) => { }
//         case Lambda(y,b) => { FreeSubsetVars(b); varsOfALambdaIncludesVarsofASubLambda(t); }
//         case Application(a,b) => { FreeSubsetVars(a); FreeSubsetVars(b); varsOfALambdaIncludesVarsofASubLambda(t); }
//     }
// }

// lemma CaSubstPrimeIsNaiveWhenFresh(M:LambdaTerm, x:Id, w:Id, ids:seq<Id>)
//     requires allUnique(ids)
//     requires includes(ids, vars(M))
//     requires w in ids
//     requires x in ids
//     requires !(w in vars(M))
//     ensures caSubstitution'(M, x, Var(w), ids) == substitution(M, x, Var(w))
//     decreases lHeight(M)
// {
//     match M {
//         case Var(y) => { }
//         case Application(a, b) => {
//             varsOfALambdaIncludesVarsofASubLambda(M);
//             CaSubstPrimeIsNaiveWhenFresh(a, x, w, ids);
//             CaSubstPrimeIsNaiveWhenFresh(b, x, w, ids);
//         }
//         case Lambda(z, P) => {
//             if z == x {
//             } else {
//                 varsOfALambdaIncludesVarsofASubLambda(M);
//                 assert z in vars(M);
//                 assert w != z;
//                 assert !(z in free(Var(w)));
//                 assert !(w in vars(P));
//                 CaSubstPrimeIsNaiveWhenFresh(P, x, w, ids);
//             }
//         }
//     }
// }

// lemma CaSubstIsNaiveWhenFresh(M:LambdaTerm, x:Id, w:Id)
//     requires !(w in vars(M))
//     ensures caSubstitution(M, x, Var(w)) == substitution(M, x, Var(w))
// {
//     var ids := reunion(vars(M), vars(Var(w)));
//     reunionIncludesBothSets(vars(M), vars(Var(w)));
//     var safe_ids := addition(x, ids);
//     CaSubstPrimeIsNaiveWhenFresh(M, x, w, safe_ids);
// }

// // Commutation of two naive variable-renamings (all four names distinct).
// lemma SubstSubstSwapVars(P:LambdaTerm, x:Id, w:Id, z:Id, zz:Id)
//     requires x != w && x != z && x != zz && w != z && w != zz && z != zz
//     ensures substitution(substitution(P,x,Var(w)), z, Var(zz))
//          == substitution(substitution(P,z,Var(zz)), x, Var(w))
//     decreases lHeight(P)
// {
//     match P {
//         case Var(u) => { }
//         case Application(a,b) => {
//             SubstSubstSwapVars(a,x,w,z,zz);
//             SubstSubstSwapVars(b,x,w,z,zz);
//         }
//         case Lambda(u,Q) => {
//             if u == x {
//             } else if u == z {
//             } else {
//                 SubstSubstSwapVars(Q,x,w,z,zz);
//             }
//         }
//     }
// }


// lemma {:vcs_split_on_every_assert} RenameThenSubstCapture(z:Id, P:LambdaTerm, x:Id, w:Id, N:LambdaTerm)
//     requires !(w in vars(P))
//     requires x != w && z != w && z != x
//     requires z in free(N)
//     ensures alphaEquivalence(caSubstitution(substitution(Lambda(z,P),x,Var(w)), w, N),
//                              caSubstitution(Lambda(z,P), x, N))
//     decreases lHeight(Lambda(z,P)), 0
// {
//     var A := Lambda(z,P);
//     var sP := substitution(P,x,Var(w));
//     assert substitution(A,x,Var(w)) == Lambda(z, sP);

//     var s2 := addition(x, addition(z, addition(w, reunion(vars(P), vars(N)))));
//     reunionIncludesBothSets(vars(P), vars(N));
//     var zz := addAnUniqueId(s2)[0];
//     assert !(zz in s2);
//     assert zz != x && zz != z && zz != w;
//     assert !(zz in vars(P)) && !(zz in vars(N));
//     FreeSubsetVars(N);
//     assert !(zz in free(N));

//     var idsP := addition(w, vars(P));
//     assert includes(idsP, vars(P));
//     newIdsDueToSubstitution(P, x, Var(w), idsP);
//     assert includes(idsP, vars(sP));
//     assert !(zz in idsP);
//     assert !(zz in vars(sP));

//     var Pzz := substitution(P, z, Var(zz));
//     var sPzz := substitution(sP, z, Var(zz));

//     SubstSubstSwapVars(P, x, w, z, zz);
//     assert sPzz == substitution(Pzz, x, Var(w));

//     SubstAlphaEquivalence(P, z, zz);
//     SubstAlphaEquivalence(sP, z, zz);

//     EqualTermsAreAlphaEquilvalent(N, N);
//     CaSubstEquivalence(Lambda(z,P), N, Lambda(zz,Pzz), N, x);
//     SubstPushesIntoSafeLambda(zz, Pzz, x, N);
//     var R := caSubstitution(A, x, N);
//     AlphaEquivTransitive(R, caSubstitution(Lambda(zz,Pzz),x,N), Lambda(zz, caSubstitution(Pzz,x,N)));

//     CaSubstEquivalence(Lambda(z,sP), N, Lambda(zz,sPzz), N, w);
//     SubstPushesIntoSafeLambda(zz, sPzz, w, N);
//     var L := caSubstitution(Lambda(z,sP), w, N);
//     AlphaEquivTransitive(L, caSubstitution(Lambda(zz,sPzz),w,N), Lambda(zz, caSubstitution(sPzz,w,N)));

//     var idsW := addition(zz, vars(P));
//     assert includes(idsW, vars(P));
//     newIdsDueToSubstitution(P, z, Var(zz), idsW);
//     assert includes(idsW, vars(Pzz));
//     assert !(w in idsW);
//     assert !(w in vars(Pzz));

//     subsitutionOfVarDoesNotChangeHeightFORVARIABLES(P, z, Var(zz));
//     RenameThenSubst(Pzz, x, w, N);
//     assert caSubstitution(sPzz,w,N) == caSubstitution(substitution(Pzz,x,Var(w)),w,N);
//     AlphaCongruenceLambda(zz, caSubstitution(sPzz,w,N), caSubstitution(Pzz,x,N));

//     AlphaEquivTransitive(L, Lambda(zz, caSubstitution(sPzz,w,N)), Lambda(zz, caSubstitution(Pzz,x,N)));
//     AlphaEquivSymmetric(R, Lambda(zz, caSubstitution(Pzz,x,N)));
//     AlphaEquivTransitive(L, Lambda(zz, caSubstitution(Pzz,x,N)), R);
// }

// lemma {:vcs_split_on_every_assert} RenameThenSubst(A:LambdaTerm, x:Id, w:Id, N:LambdaTerm)
//     requires !(w in vars(A))
//     requires x != w
//     ensures alphaEquivalence(caSubstitution(substitution(A,x,Var(w)), w, N),
//                              caSubstitution(A,x,N))
//     decreases lHeight(A), 1
// {
//     match A {
//         case Var(y) => {
//             if y == x {
//                 getVarCaSubstitution(Var(w), w, N);
//                 getVarCaSubstitution(Var(x), x, N);
//                 EqualTermsAreAlphaEquilvalent(caSubstitution(substitution(A,x,Var(w)),w,N), caSubstitution(A,x,N));
//             } else {
//                 assert y != w;
//                 getVarCaSubstitution(Var(y), w, N);
//                 getVarCaSubstitution(Var(y), x, N);
//                 EqualTermsAreAlphaEquilvalent(caSubstitution(substitution(A,x,Var(w)),w,N), caSubstitution(A,x,N));
//             }
//         }
//         case Application(a,b) => {
//             varsOfALambdaIncludesVarsofASubLambda(A);
//             assert !(w in vars(a)) && !(w in vars(b));
//             var sa := substitution(a,x,Var(w));
//             var sb := substitution(b,x,Var(w));
//             assert substitution(A,x,Var(w)) == Application(sa, sb);

//             SubstDistributesOverApp(sa, sb, w, N);
//             SubstDistributesOverApp(a, b, x, N);

//             RenameThenSubst(a,x,w,N);
//             RenameThenSubst(b,x,w,N);

//             ApplicationEquivalence(caSubstitution(sa,w,N), caSubstitution(a,x,N),
//                                    caSubstitution(sb,w,N), caSubstitution(b,x,N));
//             var L := caSubstitution(substitution(A,x,Var(w)),w,N);
//             var R := caSubstitution(A,x,N);
//             AlphaEquivSymmetric(R, Application(caSubstitution(a,x,N), caSubstitution(b,x,N)));
//             AlphaEquivTransitive(L, Application(caSubstitution(sa,w,N), caSubstitution(sb,w,N)),
//                                     Application(caSubstitution(a,x,N), caSubstitution(b,x,N)));
//             AlphaEquivTransitive(L, Application(caSubstitution(a,x,N), caSubstitution(b,x,N)), R);
//         }
//         case Lambda(z,P) => {
//             varsOfALambdaIncludesVarsofASubLambda(A);
//             assert z in vars(A) && z != w;
//             assert !(w in vars(P));
//             if z == x {
//                 assert substitution(A,x,Var(w)) == A;
//                 FreeSubsetVars(A);
//                 assert !(w in free(A));
//                 NoFreeVariablesToReplace(A, w, N);
//                 LambdaNullifiesSubstitution(P, x, N);
//                 AlphaEquivSymmetric(caSubstitution(A,w,N), A);
//                 EqualTermsAreAlphaEquilvalent(A, caSubstitution(A,x,N));
//                 AlphaEquivTransitive(caSubstitution(A,w,N), A, caSubstitution(A,x,N));
//             } else {
//                 var sP := substitution(P,x,Var(w));
//                 assert substitution(A,x,Var(w)) == Lambda(z, sP);
//                 if !(z in free(N)) {
//                     SubstPushesIntoSafeLambda(z, sP, w, N);
//                     SubstPushesIntoSafeLambda(z, P, x, N);
//                     RenameThenSubst(P,x,w,N);
//                     AlphaCongruenceLambda(z, caSubstitution(sP,w,N), caSubstitution(P,x,N));

//                     var L := caSubstitution(Lambda(z,sP), w, N);
//                     var R := caSubstitution(A, x, N);
//                     AlphaEquivTransitive(L, Lambda(z, caSubstitution(sP,w,N)), Lambda(z, caSubstitution(P,x,N)));
//                     AlphaEquivSymmetric(R, Lambda(z, caSubstitution(P,x,N)));
//                     AlphaEquivTransitive(L, Lambda(z, caSubstitution(P,x,N)), R);
//                 } else {
//                     RenameThenSubstCapture(z, P, x, w, N);
//                 }
//             }
//         }
//     }
// }


// lemma SubstRespectsBinderAlpha(x:Id, A:LambdaTerm, xx:Id, B:LambdaTerm, N:LambdaTerm)
//     requires alphaEquivalence(Lambda(x,A), Lambda(xx,B))
//     ensures alphaEquivalence(caSubstitution(A,x,N), caSubstitution(B,xx,N))
// {
//     reunionIncludesBothSets(vars(B), vars(N));
//     var inner := reunion(vars(B), vars(N));
//     var s := addition(x, addition(xx, reunion(vars(A), inner)));
//     var w := addAnUniqueId(s)[0];
//     assert !(w in s);
//     assert w != x && w != xx;
//     reunionIncludesBothSets(vars(A), inner);
//     assert !(w in vars(A)) && !(w in vars(B)) && !(w in vars(N));

//     var Aw := substitution(A, x, Var(w));
//     var Bw := substitution(B, xx, Var(w));

//     SubstAlphaEquivalence(A, x, w);
//     SubstAlphaEquivalence(B, xx, w);
//     AlphaEquivSymmetric(Lambda(x,A), Lambda(w,Aw));
//     AlphaEquivTransitive(Lambda(w,Aw), Lambda(x,A), Lambda(xx,B));
//     AlphaEquivTransitive(Lambda(w,Aw), Lambda(xx,B), Lambda(w,Bw));
//     StripSameBinder(w, Aw, Bw);

//                     EqualTermsAreAlphaEquilvalent(N, N);
//     CaSubstEquivalence(Aw, N, Bw, N, w);

//     RenameThenSubst(A, x, w, N);
//     RenameThenSubst(B, xx, w, N);

//     AlphaEquivSymmetric(caSubstitution(Aw,w,N), caSubstitution(A,x,N));
//     AlphaEquivTransitive(caSubstitution(A,x,N), caSubstitution(Aw,w,N), caSubstitution(Bw,w,N));
//     AlphaEquivTransitive(caSubstitution(A,x,N), caSubstitution(Bw,w,N), caSubstitution(B,xx,N));
//                 }


// // ===========================================================================
// // Mutually-recursive layer for alpha-invariance of parallel reduction.
// // ===========================================================================





// lemma ParRedPreservesNonFree(M:LambdaTerm, M':LambdaTerm, y:Id)
//     requires parallelReduction(M, M')
//     requires !(y in free(M))
//     ensures !(y in free(M'))
//     decreases lHeight(M)
// {
//     if alphaEquivalence(M, M') {
//         if y in free(M') { AlphaEquivSymmetric(M, M'); sameFreeForEquivalent(M', M, y); }
//     } else {
//         match M {
//             case Var(_) => { }
//             case Lambda(x, body) => {
//                 var r :| parallelReduction(body, r) && alphaEquivalence(Lambda(x, r), M');
//                 if y != x { ParRedPreservesNonFree(body, r, y); }
//                 assert !(y in free(Lambda(x, r)));
//                 if y in free(M') {
//                     AlphaEquivSymmetric(Lambda(x, r), M');
//                     sameFreeForEquivalent(M', Lambda(x, r), y);
//                 }
//             }
//             case Application(P, Q) => {
//                 if M'.Application? && parallelReduction(P, M'.t1) && parallelReduction(Q, M'.t2) {
//                     ParRedPreservesNonFree(P, M'.t1, y);
//                     ParRedPreservesNonFree(Q, M'.t2, y);
//                 } else {
//                     match P {
//                         case Lambda(z, Pb) => {
//                             var Pb', Q' :| parallelReduction(Pb, Pb') && parallelReduction(Q, Q')
//                                            && alphaEquivalence(M', caSubstitution(Pb', z, Q'));
//                             assert !(y in free(Q));
//                             ParRedPreservesNonFree(Q, Q', y);
//                             if y == z {
//                                 SubstedVarNotFree(Pb', z, Q');
//                             } else {
//                                 assert !(y in free(Pb));
//                                 ParRedPreservesNonFree(Pb, Pb', y);
//                                 TheFreeOfCaSub(Pb', z, Q', y);
//                             }
//                             assert !(y in free(caSubstitution(Pb', z, Q')));
//                             if y in free(M') {
//                                 sameFreeForEquivalent(M', caSubstitution(Pb', z, Q'), y);
//                             }
//                         }
//                         case _ => { assert false; }
//                     }
//                 }
//             }
//         }
//     }
// }

// lemma AvoidVarInTerm(M:LambdaTerm, v:Id)
//     requires !(v in free(M))
//     ensures exists M' :: alphaEquivalence(M, M') && !(v in vars(M'))
//     decreases lHeight(M)
// {
//     match M {
//         case Var(y) => { EqualTermsAreAlphaEquilvalent(M, M); }
//         case Application(P, Q) => {
//             AvoidVarInTerm(P, v);
//             var P' :| alphaEquivalence(P, P') && !(v in vars(P'));
//             AvoidVarInTerm(Q, v);
//             var Q' :| alphaEquivalence(Q, Q') && !(v in vars(Q'));
//             ApplicationEquivalence(P, P', Q, Q');
//             reunionIncludesBothSets(vars(P'), vars(Q'));
//             assert !(v in vars(Application(P', Q')));
//         }
//         case Lambda(z, body) => {
//             varsOfALambdaIncludesVarsofASubLambda(M);
//             if z == v {
//                 var zf := addAnUniqueId(vars(M))[0];
//                 assert !(zf in vars(M)) && !(zf in vars(body));
//                 var br := substitution(body, v, Var(zf));
//                 SubstAlphaEquivalence(body, v, zf);
//                 subsitutionOfVarDoesNotChangeHeightFORVARIABLES(body, v, Var(zf));
//                 NaiveSubstRemovesVar(body, v, zf);
//                 AvoidVarInTerm(br, v);
//                 var br2 :| alphaEquivalence(br, br2) && !(v in vars(br2));
//                 AlphaCongruenceLambda(zf, br, br2);
//                 AlphaEquivTransitive(M, Lambda(zf, br), Lambda(zf, br2));
//                 assert !(v in vars(Lambda(zf, br2)));
//             } else {
//                 assert !(v in free(body));
//                 AvoidVarInTerm(body, v);
//                 var body2 :| alphaEquivalence(body, body2) && !(v in vars(body2));
//                 AlphaCongruenceLambda(z, body, body2);
//                 assert !(v in vars(Lambda(z, body2)));
//             }
//         }
//     }
// }

// lemma ParRedLambdaIntro(zf:Id, body:LambdaTerm, rr:LambdaTerm, t2:LambdaTerm)
//     requires parallelReduction(body, rr) && alphaEquivalence(Lambda(zf, rr), t2)
//     ensures parallelReduction(Lambda(zf, body), t2)
// { }
// lemma ParRedBetaIntro(zf:Id, PbA:LambdaTerm, QA:LambdaTerm, P2:LambdaTerm, N2:LambdaTerm, t2:LambdaTerm)
//     requires parallelReduction(PbA, P2) && parallelReduction(QA, N2)
//     requires alphaEquivalence(t2, caSubstitution(P2, zf, N2))
//     ensures parallelReduction(Application(Lambda(zf, PbA), QA), t2)
// { }
// lemma ParRedCongIntro(PA:LambdaTerm, QA:LambdaTerm, PpA:LambdaTerm, QpA:LambdaTerm)
//     requires parallelReduction(PA, PpA) && parallelReduction(QA, QpA)
//     ensures parallelReduction(Application(PA, QA), Application(PpA, QpA))
// { }

// lemma {:vcs_split_on_every_assert} ParRedRename(M:LambdaTerm, M':LambdaTerm, a:Id, b:Id)
//     requires parallelReduction(M, M')
//     ensures parallelReduction(caSubstitution(M, a, Var(b)), caSubstitution(M', a, Var(b)))
//     decreases lHeight(M), 1
// {
//     var Mca := caSubstitution(M, a, Var(b));
//     var M'ca := caSubstitution(M', a, Var(b));
//     if alphaEquivalence(M, M') {
//         EqualTermsAreAlphaEquilvalent(Var(b), Var(b));
//         CaSubstEquivalence(M, Var(b), M', Var(b), a);
//         return;
//     }
//     match M {
//         case Var(z) => { assert false; }
//         case Lambda(z, body) => {
//             var s :| parallelReduction(body, s) && alphaEquivalence(Lambda(z, s), M');
//             var S := addition(a, addition(b, reunion(vars(M), reunion(vars(M'), vars(s)))));
//             reunionIncludesBothSets(vars(M'), vars(s));
//             reunionIncludesBothSets(vars(M), reunion(vars(M'), vars(s)));
//             var zf := addAnUniqueId(S)[0];
//             assert !(zf in S);
//             assert zf != a && zf != b;
//             varsOfALambdaIncludesVarsofASubLambda(M);
//             assert !(zf in vars(M)) && !(zf in vars(M')) && !(zf in vars(s));
//             assert !(zf in vars(body));

//             var body_alt := substitution(body, z, Var(zf));
//             var s_alt := substitution(s, z, Var(zf));

//             ParRedRename(body, s, z, zf);
//             CaSubstIsNaiveWhenFresh(body, z, zf);
//             CaSubstIsNaiveWhenFresh(s, z, zf);
//             assert parallelReduction(body_alt, s_alt);

//             subsitutionOfVarDoesNotChangeHeightFORVARIABLES(body, z, Var(zf));
//             ParRedRename(body_alt, s_alt, a, b);
//             var PbA := caSubstitution(body_alt, a, Var(b));
//             var rr := caSubstitution(s_alt, a, Var(b));
//             assert parallelReduction(PbA, rr);

//             SubstAlphaEquivalence(body, z, zf);
//             EqualTermsAreAlphaEquilvalent(Var(b), Var(b));
//             CaSubstEquivalence(M, Var(b), Lambda(zf, body_alt), Var(b), a);
//             SubstPushesIntoSafeLambda(zf, body_alt, a, Var(b));
//             AlphaEquivTransitive(Mca, caSubstitution(Lambda(zf, body_alt), a, Var(b)), Lambda(zf, PbA));

//             SubstAlphaEquivalence(s, z, zf);
//             AlphaEquivTransitive(Lambda(zf, s_alt), Lambda(z, s), M');
//             CaSubstEquivalence(Lambda(zf, s_alt), Var(b), M', Var(b), a);
//             SubstPushesIntoSafeLambda(zf, s_alt, a, Var(b));
//             AlphaEquivSymmetric(caSubstitution(Lambda(zf, s_alt), a, Var(b)), Lambda(zf, rr));
//             AlphaEquivTransitive(Lambda(zf, rr), caSubstitution(Lambda(zf, s_alt), a, Var(b)), M'ca);

//             ParRedLambdaIntro(zf, PbA, rr, M'ca);
//             AlphaEquivSymmetric(Mca, Lambda(zf, PbA));
//             EqualTermsAreAlphaEquilvalent(M'ca, M'ca);
//             CaSubsitutionOfVarDoesNotChangeHeightFORVARIABLES(body_alt, a, Var(b));
//             ParallelReductionAlphaInvariance(Lambda(zf, PbA), M'ca, Mca, M'ca);
//         }
//         case Application(P, Q) => {
//             if M'.Application? && parallelReduction(P, M'.t1) && parallelReduction(Q, M'.t2) {
//                 var Pp := M'.t1;
//                 var Qp := M'.t2;
//                 SubstDistributesOverApp(P, Q, a, Var(b));
//                 SubstDistributesOverApp(Pp, Qp, a, Var(b));
//                 ParRedRename(P, Pp, a, b);
//                 ParRedRename(Q, Qp, a, b);
//                 var PA := caSubstitution(P, a, Var(b));
//                 var QA := caSubstitution(Q, a, Var(b));
//                 var PpA := caSubstitution(Pp, a, Var(b));
//                 var QpA := caSubstitution(Qp, a, Var(b));
//                 ParRedCongIntro(PA, QA, PpA, QpA);
//                 AlphaEquivSymmetric(Mca, Application(PA, QA));
//                 AlphaEquivSymmetric(M'ca, Application(PpA, QpA));
//                 CaSubsitutionOfVarDoesNotChangeHeightFORVARIABLES(P, a, Var(b));
//                 CaSubsitutionOfVarDoesNotChangeHeightFORVARIABLES(Q, a, Var(b));
//                 ParallelReductionAlphaInvariance(Application(PA, QA), Application(PpA, QpA), Mca, M'ca);
//             } else {
//                 match P {
//                     case Lambda(z, Pb) => {
//                         var Pb', Q'' :| parallelReduction(Pb, Pb') && parallelReduction(Q, Q'')
//                                         && alphaEquivalence(M', caSubstitution(Pb', z, Q''));
//                         var S := addition(a, addition(b, reunion(vars(M), reunion(vars(M'),
//                                     reunion(vars(Pb'), vars(Q''))))));
//                         reunionIncludesBothSets(vars(Pb'), vars(Q''));
//                         reunionIncludesBothSets(vars(M'), reunion(vars(Pb'), vars(Q'')));
//                         reunionIncludesBothSets(vars(M), reunion(vars(M'), reunion(vars(Pb'), vars(Q''))));
//                         var zf := addAnUniqueId(S)[0];
//                         assert !(zf in S);
//                         assert zf != a && zf != b;
//                         varsOfALambdaIncludesVarsofASubLambda(M);
//                         varsOfALambdaIncludesVarsofASubLambda(P);
//                         assert !(zf in vars(M)) && !(zf in vars(M')) && !(zf in vars(Pb')) && !(zf in vars(Q''));
//                         assert !(zf in vars(P));
//                         assert !(zf in vars(Pb)) && !(zf in vars(Q));

//                         var Pb_alt := substitution(Pb, z, Var(zf));
//                         var Pb'_alt := substitution(Pb', z, Var(zf));

//                         assert parallelReduction(Pb, Pb');
//                         assert lHeight(Pb) < lHeight(M);
//                         ParRedRename(Pb, Pb', z, zf);
//                         CaSubstIsNaiveWhenFresh(Pb, z, zf);
//                         CaSubstIsNaiveWhenFresh(Pb', z, zf);
//                         assert parallelReduction(Pb_alt, Pb'_alt);

//                         subsitutionOfVarDoesNotChangeHeightFORVARIABLES(Pb, z, Var(zf));
//                         var PbA := caSubstitution(Pb_alt, a, Var(b));
//                         var QA := caSubstitution(Q, a, Var(b));
//                         var P2 := caSubstitution(Pb'_alt, a, Var(b));
//                         var N2 := caSubstitution(Q'', a, Var(b));

//                         ParRedRename(Pb_alt, Pb'_alt, a, b);
//                         ParRedRename(Q, Q'', a, b);
//                         assert parallelReduction(PbA, P2);
//                         assert parallelReduction(QA, N2);

//                         var LHSapp := Application(Lambda(zf, PbA), QA);

//                         SubstAlphaEquivalence(Pb, z, zf);
//                         EqualTermsAreAlphaEquilvalent(Q, Q);
//                         ApplicationEquivalence(Lambda(z, Pb), Lambda(zf, Pb_alt), Q, Q);
//                         EqualTermsAreAlphaEquilvalent(Var(b), Var(b));
//                         CaSubstEquivalence(M, Var(b), Application(Lambda(zf, Pb_alt), Q), Var(b), a);
//                         SubstDistributesOverApp(Lambda(zf, Pb_alt), Q, a, Var(b));
//                         SubstPushesIntoSafeLambda(zf, Pb_alt, a, Var(b));
//                         EqualTermsAreAlphaEquilvalent(QA, QA);
//                         ApplicationEquivalence(caSubstitution(Lambda(zf, Pb_alt), a, Var(b)), Lambda(zf, PbA), QA, QA);
//                         AlphaEquivTransitive(Mca,
//                                              caSubstitution(Application(Lambda(zf, Pb_alt), Q), a, Var(b)),
//                                              Application(caSubstitution(Lambda(zf, Pb_alt), a, Var(b)), QA));
//                         AlphaEquivTransitive(Mca,
//                                              Application(caSubstitution(Lambda(zf, Pb_alt), a, Var(b)), QA),
//                                              LHSapp);

//                         SubstAlphaEquivalence(Pb', z, zf);
//                         SubstRespectsBinderAlpha(z, Pb', zf, Pb'_alt, Q'');
//                         AlphaEquivTransitive(M', caSubstitution(Pb', z, Q''), caSubstitution(Pb'_alt, zf, Q''));
//                         EqualTermsAreAlphaEquilvalent(Var(b), Var(b));
//                         CaSubstEquivalence(M', Var(b), caSubstitution(Pb'_alt, zf, Q''), Var(b), a);
//                         SubstitutionLemma(Pb'_alt, Q'', Var(b), zf, a);
//                         AlphaEquivTransitive(M'ca,
//                                              caSubstitution(caSubstitution(Pb'_alt, zf, Q''), a, Var(b)),
//                                              caSubstitution(P2, zf, N2));

//                         ParRedBetaIntro(zf, PbA, QA, P2, N2, M'ca);
//                         AlphaEquivSymmetric(Mca, LHSapp);
//                         EqualTermsAreAlphaEquilvalent(M'ca, M'ca);
//                         CaSubsitutionOfVarDoesNotChangeHeightFORVARIABLES(Pb_alt, a, Var(b));
//                         CaSubsitutionOfVarDoesNotChangeHeightFORVARIABLES(Q, a, Var(b));
//                         ParallelReductionAlphaInvariance(LHSapp, M'ca, Mca, M'ca);
//                     }
//                     case _ => { assert false; }
//                 }
//             }
//         }
//     }
// }

// lemma {:vcs_split_on_every_assert} ParRedAlphaUnderBinder(x:Id, B:LambdaTerm, R:LambdaTerm, x2:Id, B2arg:LambdaTerm)
//     requires parallelReduction(B, R)
//     requires alphaEquivalence(Lambda(x, B), Lambda(x2, B2arg))
//     ensures exists RR :: parallelReduction(B2arg, RR) && alphaEquivalence(Lambda(x2, RR), Lambda(x, R))
//     decreases lHeight(B), 2
// {
//     if x == x2 {
//         StripSameBinder(x, B, B2arg);
//         EqualTermsAreAlphaEquilvalent(R, R);
//         ParallelReductionAlphaInvariance(B, R, B2arg, R);
//         EqualTermsAreAlphaEquilvalent(Lambda(x2, R), Lambda(x, R));
//         assert parallelReduction(B2arg, R) && alphaEquivalence(Lambda(x2, R), Lambda(x, R));
//     } else {
//         BinderRenameNotFree(x, B, x2, B2arg);
//         ParRedPreservesNonFree(B, R, x2);
//         AvoidVarInTerm(B, x2);
//         var Bc :| alphaEquivalence(B, Bc) && !(x2 in vars(Bc));
//         AvoidVarInTerm(R, x2);
//         var Rc :| alphaEquivalence(R, Rc) && !(x2 in vars(Rc));

//         AlphaSameHeight(B, Bc);
//         ParallelReductionAlphaInvariance(B, R, Bc, Rc);

//         AlphaEquivSymmetric(B, Bc);
//         AlphaCongruenceLambda(x, Bc, B);
//         AlphaEquivTransitive(Lambda(x, Bc), Lambda(x, B), Lambda(x2, B2arg));

//         ParRedRename(Bc, Rc, x, x2);
//         var BcS := caSubstitution(Bc, x, Var(x2));
//         var RR := caSubstitution(Rc, x, Var(x2));
//         assert parallelReduction(BcS, RR);

//         CaSubstIsNaiveWhenFresh(Bc, x, x2);
//         SubstAlphaEquivalence(Bc, x, x2);
//         AlphaEquivSymmetric(Lambda(x, Bc), Lambda(x2, B2arg));
//         AlphaEquivTransitive(Lambda(x2, B2arg), Lambda(x, Bc), Lambda(x2, BcS));
//         StripSameBinder(x2, B2arg, BcS);
//         AlphaEquivSymmetric(B2arg, BcS);

//         CaSubsitutionOfVarDoesNotChangeHeightFORVARIABLES(Bc, x, Var(x2));
//         EqualTermsAreAlphaEquilvalent(RR, RR);
//         ParallelReductionAlphaInvariance(BcS, RR, B2arg, RR);

//         CaSubstIsNaiveWhenFresh(Rc, x, x2);
//         SubstAlphaEquivalence(Rc, x, x2);
//         AlphaEquivSymmetric(R, Rc);
//         AlphaCongruenceLambda(x, Rc, R);
//         AlphaEquivSymmetric(Lambda(x, Rc), Lambda(x2, RR));
//         AlphaEquivTransitive(Lambda(x2, RR), Lambda(x, Rc), Lambda(x, R));

//         assert parallelReduction(B2arg, RR) && alphaEquivalence(Lambda(x2, RR), Lambda(x, R));
//     }
// }

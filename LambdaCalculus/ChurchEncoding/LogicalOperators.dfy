include "ChurchEncoding.dfy"
include "NormalOrder.dfy"
lemma andTrueTrue(and:LambdaTerm, tru:LambdaTerm) 
    requires and==andVal() && tru==trueVal()
    ensures var andtruetrue:=Application(Application(and, tru), tru);
    normalOrderHalts(andtruetrue) && isTrue(normalOrder(andtruetrue))
{
    var s0 := Application(Application(and, tru), tru);
    var help1    := Lambda(1, Application(Application(tru, Var(1)), tru));
    var s1 := Application(help1, tru);
    var s2    := Application(Application(tru, tru), tru);
    var s3    := Application(Lambda(1, tru), tru);

    assert normalOrderStep(s0)     == Some(s1);
    assert normalOrderStep(s1)     == Some(s2);
    assert normalOrderStep(s2)        == Some(s3);
    assert normalOrderStep(s3)        == Some(tru);
    assert trueVal()==tru;
    assert normalOrderStep(tru) == None;


    assert normalOrder'(s0,      4) == normalOrder'(s1, 3);
    assert normalOrder'(s1,      3) == normalOrder'(s2,    2);
    assert normalOrder'(s2,         2) == normalOrder'(s3,    1);
    assert normalOrder'(s3,         1) == normalOrder'(tru, 0);
    assert normalOrder'(tru,  0) == tru;
    assert normalOrder'(s0,      4) == tru;

    forall m:nat | normalOrderEndsInNSteps(s0, m)
        ensures normalOrder'(s0, m) == tru
    {
        normalOrderStepsUnique(s0, 4, m); 
    }
    assert normalOrder(s0) == tru;

}
lemma andFalseFalse(and:LambdaTerm,fals:LambdaTerm)
    requires and==andVal() && fals==falseVal()
    ensures var andfalsefalse:=Application(Application(and, fals), fals);
    normalOrderHalts(andfalsefalse) && isFalse(normalOrder(andfalsefalse))
{
    var one:=Var(1);
    var oneId:=1;
    var s0:=Application(Application(and, fals), fals);
    var help1:=Lambda(oneId,Application(Application(fals,one),fals));
    var s1:=Application(help1,fals);
    var s2:= Application(Application(fals,fals),fals);
    var s3:= Application(Lambda(1,Var(1)),fals);

    assert normalOrderStep(s0)     == Some(s1);
    assert normalOrderStep(s1)     == Some(s2);
    assert normalOrderStep(s2)        == Some(s3);
    assert normalOrderStep(s3)        == Some(fals);
    assert falseVal()==fals;
    assert normalOrderStep(fals) == None;


    assert normalOrder'(s0,      4) == normalOrder'(s1, 3);
    assert normalOrder'(s1,      3) == normalOrder'(s2,    2);
    assert normalOrder'(s2,         2) == normalOrder'(s3,    1);
    assert normalOrder'(s3,         1) == normalOrder'(fals, 0);
    assert normalOrder'(fals,  0) == fals;
    assert normalOrder'(s0,      4) == fals;

    forall m:nat | normalOrderEndsInNSteps(s0, m)
        ensures normalOrder'(s0, m) == fals
    {
        normalOrderStepsUnique(s0, 4, m); 
    }
    assert normalOrder(s0) == fals;
    

}
lemma andFalseTrue(and:LambdaTerm,fals:LambdaTerm,tru:LambdaTerm)
    requires and==andVal() && fals==falseVal() && tru==trueVal()
    ensures var final:=Application(Application(and, fals), tru);
    normalOrderHalts(final) && isFalse(normalOrder(final))
{
    var and := andVal(); var fals := falseVal(); var tru := trueVal();
    var s0    := Application(Application(and, fals), tru);
    var help1 := Lambda(1, Application(Application(fals, Var(1)), fals));
    var s1    := Application(help1, tru);
    var s2    := Application(Application(fals, tru), fals);
    var s3    := Application(Lambda(1, Var(1)), fals);

    assert normalOrderStep(s0)     == Some(s1);
    assert normalOrderStep(s1)     == Some(s2);
    assert normalOrderStep(s2)        == Some(s3);
    assert normalOrderStep(s3)        == Some(fals);
    assert falseVal()==fals;
    assert normalOrderStep(fals) == None;


    assert normalOrder'(s0,      4) == normalOrder'(s1, 3);
    assert normalOrder'(s1,      3) == normalOrder'(s2,    2);
    assert normalOrder'(s2,         2) == normalOrder'(s3,    1);
    assert normalOrder'(s3,         1) == normalOrder'(fals, 0);
    assert normalOrder'(fals,  0) == fals;
    assert normalOrder'(s0,      4) == fals;

    forall m:nat | normalOrderEndsInNSteps(s0, m)
        ensures normalOrder'(s0, m) == fals
    {
        normalOrderStepsUnique(s0, 4, m); 
    }
    assert normalOrder(s0) == fals;
}
lemma andTrueFalse(and:LambdaTerm,tru:LambdaTerm,fals:LambdaTerm)
    requires and==andVal() && tru==trueVal() && fals==falseVal()
    ensures var andtruetrue:=Application(Application(and, tru), fals);
    normalOrderHalts(andtruetrue) && isFalse(normalOrder(andtruetrue))

{

    var and := andVal(); var tru := trueVal(); var fals := falseVal();
    var s0    := Application(Application(and, tru), fals);
    var help1 := Lambda(1, Application(Application(tru, Var(1)), tru));
    var s1    := Application(help1, fals);
    var s2    := Application(Application(tru, fals), tru);
    var s3    := Application(Lambda(1, fals), tru);

    assert normalOrderStep(s0)     == Some(s1);
    assert normalOrderStep(s1)     == Some(s2);
    assert normalOrderStep(s2)        == Some(s3);
    assert normalOrderStep(s3)        == Some(fals);
    assert falseVal()==fals;
    assert normalOrderStep(fals) == None;

    forall m:nat | normalOrderEndsInNSteps(s0, m)
        ensures normalOrder'(s0, m) == fals
    {
        normalOrderStepsUnique(s0, 4, m); 
    }

    assert normalOrder'(s0,      4) == normalOrder'(s1, 3);
    assert normalOrder'(s1,      3) == normalOrder'(s2,    2);
    assert normalOrder'(s2,         2) == normalOrder'(s3,    1);
    assert normalOrder'(Application(Lambda(1, fals), tru),         1) == normalOrder'(fals, 0);
    assert normalOrder'(fals,  0) == fals;
    assert normalOrder'(s0,      4) == fals;

    assert normalOrder(s0) == fals;
}

lemma orTrueTrue(or:LambdaTerm,tru:LambdaTerm)
    requires or==orVal() && tru==trueVal()
    ensures var ortruetrue:=Application(Application(or,tru),tru);
    normalOrderHalts(ortruetrue) && isTrue(normalOrder(ortruetrue))
{
    var s0    := Application(Application(or, tru), tru);
    var help1 := Lambda(1, Application(Application(tru, tru), Var(1)));
    var s1    := Application(help1, tru);
    var s2    := Application(Application(tru, tru), tru);
    var s3    := Application(Lambda(1, tru), tru);

    assert normalOrderStep(s0)     == Some(s1);
    assert normalOrderStep(s1)     == Some(s2);
    assert normalOrderStep(s2)        == Some(s3);
    assert normalOrderStep(s3)        == Some(tru);
    assert trueVal()==tru;
    assert normalOrderStep(tru) == None;

    forall m:nat | normalOrderEndsInNSteps(s0, m)
        ensures normalOrder'(s0, m) == tru
    {
        normalOrderStepsUnique(s0, 4, m); 
    }

    assert normalOrderEndsInNSteps(s0,4);

    assert normalOrder'(s0,      4) == normalOrder'(s1, 3);
    assert normalOrder'(s1,      3) == normalOrder'(s2,    2);
    assert normalOrder'(s2,         2) == normalOrder'(s3,    1);
    assert normalOrder'(Application(Lambda(1, tru), tru),         1) == normalOrder'(tru, 0);
    assert normalOrder'(tru,  0) == tru;
    assert normalOrder'(s0,      4) == tru;

    assert normalOrder(s0) == tru;
}

lemma orTrueFalse(or:LambdaTerm,tru:LambdaTerm,fals:LambdaTerm)
    requires or==orVal() && tru==trueVal() && fals==falseVal()
    ensures var ortruefalse:=Application(Application(or,tru),fals);
    normalOrderHalts(ortruefalse) && isTrue(normalOrder(ortruefalse))
{

    var or := orVal(); var tru := trueVal(); var fals := falseVal();
    var s0    := Application(Application(or, tru), fals);
    var help1 := Lambda(1, Application(Application(tru, tru), Var(1)));
    var s1    := Application(help1, fals);
    var s2    := Application(Application(tru, tru), fals);
    var s3    := Application(Lambda(1, tru), fals);

    assert normalOrderStep(s0)     == Some(s1);
    assert normalOrderStep(s1)     == Some(s2);
    assert normalOrderStep(s2)        == Some(s3);
    assert normalOrderStep(s3)        == Some(tru);
    assert trueVal()==tru;
    assert normalOrderStep(tru) == None;

    forall m:nat | normalOrderEndsInNSteps(s0, m)
        ensures normalOrder'(s0, m) == tru
    {
        normalOrderStepsUnique(s0, 4, m); 
    }

    assert normalOrderEndsInNSteps(s0,4);

    assert normalOrder'(s0,      4) == normalOrder'(s1, 3);
    assert normalOrder'(s1,      3) == normalOrder'(s2,    2);
    assert normalOrder'(s2,         2) == normalOrder'(s3,    1);
    assert normalOrder'(s3,         1) == normalOrder'(tru, 0);
    assert normalOrder'(tru,  0) == tru;
    assert normalOrder'(s0,      4) == tru;

    assert normalOrder(s0) == tru;
}

lemma orFalseFalse(or:LambdaTerm,fals:LambdaTerm)
    requires or==orVal() && fals==falseVal()
    ensures var orfalsefalse:=Application(Application(or,fals),fals);
    normalOrderHalts(orfalsefalse) && isFalse(normalOrder(orfalsefalse))
{

    var or := orVal(); var fals := falseVal();
    var s0    := Application(Application(or, fals), fals);
    var help1 := Lambda(1, Application(Application(fals, fals), Var(1)));
    var s1    := Application(help1, fals);
    var s2    := Application(Application(fals, fals), fals);
    var s3    := Application(Lambda(1, Var(1)), fals);

    assert normalOrderStep(s0)     == Some(s1);
    assert normalOrderStep(s1)     == Some(s2);
    assert normalOrderStep(s2)        == Some(s3);
    assert normalOrderStep(s3)        == Some(fals);
    assert falseVal()==fals;
    assert normalOrderStep(fals) == None;

    forall m:nat | normalOrderEndsInNSteps(s0, m)
        ensures normalOrder'(s0, m) == fals
    {
        normalOrderStepsUnique(s0, 4, m); 
    }

    assert normalOrder'(s0,      4) == normalOrder'(s1, 3);
    assert normalOrder'(s1,      3) == normalOrder'(s2,    2);
    assert normalOrder'(s2,         2) == normalOrder'(s3,    1);
    assert normalOrder'(s3,         1) == normalOrder'(fals, 0);
    assert normalOrder'(fals,  0) == fals;
    assert normalOrder'(s0,      4) == fals;

    assert normalOrder(s0) == fals;
}

lemma orFalseTrue(or:LambdaTerm,tru:LambdaTerm,fals:LambdaTerm)
    requires or==orVal() && tru==trueVal() && fals==falseVal()
    ensures var orfalsetrue:=Application(Application(or,fals),tru);
    normalOrderHalts(orfalsetrue) && isTrue(normalOrder(orfalsetrue))
{

    var or := orVal(); var fals := falseVal(); var tru := trueVal();
    var s0    := Application(Application(or, fals), tru);
    var help1 := Lambda(1, Application(Application(fals, fals), Var(1)));
    var s1    := Application(help1, tru);
    var s2    := Application(Application(fals, fals), tru);
    var s3    := Application(Lambda(1, Var(1)), tru);

    assert normalOrderStep(s0)     == Some(s1);
    assert normalOrderStep(s1)     == Some(s2);
    assert normalOrderStep(s2)        == Some(s3);
    assert normalOrderStep(s3)        == Some(tru);
    assert trueVal()==tru;
    assert normalOrderStep(tru) == None;

    forall m:nat | normalOrderEndsInNSteps(s0, m)
        ensures normalOrder'(s0, m) == tru
    {
        normalOrderStepsUnique(s0, 4, m); 
    }

    assert normalOrder'(s0,      4) == normalOrder'(s1, 3);
    assert normalOrder'(s1,      3) == normalOrder'(s2,    2);
    assert normalOrder'(s2,         2) == normalOrder'(s3,    1);
    assert normalOrder'(Application(Lambda(1, tru), tru),         1) == normalOrder'(tru, 0);
    assert normalOrder'(tru,  0) == tru;
    assert normalOrder'(s0,      4) == tru;

    assert normalOrder(s0) == tru;
}


lemma notTrue(not:LambdaTerm,tru:LambdaTerm)
    requires not==notVal() && tru==trueVal()
    ensures var nottrue:=Application(not,tru);
    normalOrderHalts(nottrue) && isFalse(normalOrder(nottrue))
{
    var fals:=falseVal();
    var s0 := Application(not, tru);
    var s1 := Application(Application(tru, fals), tru);
    var s2 := Application(Lambda(1, fals), tru);

    assert normalOrderStep(s0)     == Some(s1);
    assert normalOrderStep(s1)     == Some(s2);
    assert normalOrderStep(s2)        == Some(fals);
    assert falseVal()==fals;
    assert normalOrderStep(fals) == None;

    forall m:nat | normalOrderEndsInNSteps(s0, m)
        ensures normalOrder'(s0, m) == fals
    {
        normalOrderStepsUnique(s0, 3, m); 
    }

    assert normalOrder'(s0,      3) == normalOrder'(s1, 2);
    assert normalOrder'(s1,      2) == normalOrder'(s2,    1);
    assert 1>0;
    assert normalOrder'(s2,         1) == normalOrder'(fals, 0);
    assert normalOrder'(fals,  0) == fals;
    assert normalOrder'(s0,      3) == fals;

    assert normalOrderEndsInNSteps(s0,3);

    assert normalOrder(s0) == fals;
}

lemma notFalse(not:LambdaTerm,fals:LambdaTerm)
    requires not==notVal() && fals==falseVal()
    ensures var notfalse:=Application(not,fals);
    normalOrderHalts(notfalse) && isTrue(normalOrder(notfalse))
{
    var tru:=trueVal();
    var s0 := Application(not, fals);
    var s1 := Application(Application(fals, fals), tru);
    var s2 := Application(Lambda(1, Var(1)), tru);

    assert normalOrderStep(s0)     == Some(s1);
    assert normalOrderStep(s1)     == Some(s2);
    assert normalOrderStep(s2)        == Some(tru);
    assert trueVal()==tru;
    assert normalOrderStep(tru) == None;

    forall m:nat | normalOrderEndsInNSteps(s0, m)
        ensures normalOrder'(s0, m) == tru
    {
        normalOrderStepsUnique(s0, 3, m); 
    }

    assert normalOrder'(s0,      3) == normalOrder'(s1, 2);
    assert normalOrder'(s1,      2) == normalOrder'(s2,    1);
    assert normalOrder'(s2,         1) == normalOrder'(tru, 0);
    assert normalOrder'(tru,  0) == tru;
    assert normalOrder'(s0,      3) == tru;

    assert normalOrderEndsInNSteps(s0,3);

    assert normalOrder(s0) == tru;
}

// defineste confluenta p
// alfa echivalenta 
//
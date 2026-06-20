include "./../objects.dfy"
include "Substitutions.dfy"




predicate alphaEquivalence(t1:LambdaTerm,t2:LambdaTerm)

{
    alphaEquivalence'(t1,t2,[],[])
}


predicate alphaEquivalence'(t1:LambdaTerm,t2:LambdaTerm,id1:seq<Id>,id2:seq<Id>)
    decreases minim(lHeight(t1),lHeight(t2))

{
    
    match t1
        case Var(x) => (match t2 
                            case Var(y) => (
                                var r1:=findId(id1,x);
                                var r2:=findId(id2,y);
                                r1==r2 
                                &&
                                match r1
                                    case None => x==y
                                    case Some(_) => true 
                            )
                            case _ => false
                        ) 
        case Lambda(x,t1') => (match t2
                                case Lambda(y,t2') => 

                                    alphaEquivalence'(t1',t2',id1+[x],id2+[y])
                                case _=> false)
        case Application(t1',t1'') => match t2
                                        case Application(t2',t2'')=> alphaEquivalence'(t1',t2',id1,id2) && alphaEquivalence'(t1'',t2'',id1,id2)
                                        case _=>false
}

lemma AlphaSameHeight(t1:LambdaTerm, t2:LambdaTerm)
    requires alphaEquivalence(t1, t2)
    ensures lHeight(t1) == lHeight(t2)
{ AlphaSameHeight'(t1, t2, [], []); }


lemma AlphaSameHeight'(t1:LambdaTerm, t2:LambdaTerm, id1:seq<Id>, id2:seq<Id>)
    requires alphaEquivalence'(t1, t2, id1, id2)
    ensures lHeight(t1) == lHeight(t2)
    decreases lHeight(t1)
{
    match t1 {
        case Var(_) => { }
        case Lambda(x, b) => {
            var y, b2 :| t2 == Lambda(y, b2);
            AlphaSameHeight'(b, b2, id1+[x], id2+[y]);
        }
        case Application(a, b) => {
            var a2, b2 :| t2 == Application(a2, b2);
            AlphaSameHeight'(a, a2, id1, id2);
            AlphaSameHeight'(b, b2, id1, id2);
        }
    }
}

lemma AlphaEquivSymmetric(t1:LambdaTerm, t2:LambdaTerm)
    requires alphaEquivalence(t1, t2)
    ensures alphaEquivalence(t2, t1)
{
    AlphaEquivSymmetric'(t1,t2,[],[]);
}
lemma AlphaEquivSymmetric'(t1:LambdaTerm, t2:LambdaTerm,id1:seq<Id>,id2:seq<Id>)
    requires alphaEquivalence'(t1, t2,id1,id2)
    ensures alphaEquivalence'(t2, t1,id2,id1)
{


}


lemma ApplicationEquivalence(t1a:LambdaTerm,t2a:LambdaTerm,t1b:LambdaTerm,t2b:LambdaTerm)
    requires alphaEquivalence(t1a,t2a) && alphaEquivalence(t1b,t2b)
    ensures alphaEquivalence(Application(t1a,t1b),Application(t2a,t2b))
{

}

lemma AlphaEquivTransitive(t1:LambdaTerm, t2:LambdaTerm, t3:LambdaTerm)
    requires alphaEquivalence(t1, t2)
    requires alphaEquivalence(t2, t3)
    ensures alphaEquivalence(t1, t3)
{
    AlphaEquivTransitive'(t1,t2,t3,[],[],[]);
}


lemma AlphaEquivTransitive'(t1:LambdaTerm, t2:LambdaTerm, t3:LambdaTerm,id1:seq<Id>,id2:seq<Id>,id3:seq<Id>)
    requires alphaEquivalence'(t1, t2,id1,id2)
    requires alphaEquivalence'(t2, t3,id2,id3)
    ensures alphaEquivalence'(t1, t3,id1,id3)
{
    
}


lemma ApplicationEquivalenceDown (t1a:LambdaTerm,t1b:LambdaTerm,t2a:LambdaTerm,t2b:LambdaTerm)
    requires alphaEquivalence(Application(t1a,t1b),Application(t2a,t2b))
    ensures alphaEquivalence(t1a,t2a) && alphaEquivalence(t1b,t2b)
{

}


lemma EqualTermsAreAlphaEquilvalent(t1:LambdaTerm,t2:LambdaTerm)
    requires t1==t2 
    ensures alphaEquivalence(t1,t2)
{
    EqualTermsAreAlphaEquilvalent'(t1,t2,[],[]);
}

lemma NonApplicationAlphaEquivalence(t1: LambdaTerm, t2: LambdaTerm)
    requires t1.Application? && alphaEquivalence(t1, t2)
    ensures t2.Application?
{ }

lemma NonLambdaAlphaEquivalence(t1: LambdaTerm, t2: LambdaTerm)
    requires t1.Lambda?
    requires alphaEquivalence(t1, t2)
    ensures t2.Lambda?
{
    
}

lemma EqualTermsAreAlphaEquilvalent'(t1:LambdaTerm,t2:LambdaTerm,id1:seq<Id>,id2:seq<Id>)
    requires forall y :: y in vars(t1) ==> findId(id1, y) == findId(id2, y)
    requires |id1|==|id2|
    requires t1==t2 
    ensures alphaEquivalence'(t1,t2,id1,id2)
    decreases minim(lHeight(t1),lHeight(t2))
{
        match t1
            case Var(x) => {
                assert t1==t2;
                var y:|t2==Var(y);
                assert x==y;
                var r1:=findId(id1,x);
                var r2:=findId(id2,y);
                assert r1==r2;
                if (r1==None)
                {
                    assert x==y;
                }
                assert alphaEquivalence'(t1,t2,id1,id2);
            }
            case Lambda(x,t1') => {
                var y,t2':|t2==Lambda(y,t2');
                assert y==x && t2'==t1';
                var id1':=id1+[x];
                var id2':=id2+[y];
                assert findId(id1',x)==Some(|id1'|-1);
                assert findId(id1',x)==findId(id2',y);
                EqualTermsAreAlphaEquilvalent'(t1',t2',id1+[x],id2+[y]);
            }
            case Application(t1',t1'') => {
                var t2',t2'':|t2==Application(t2',t2'');
                EqualTermsAreAlphaEquilvalent'(t1',t2',id1,id2);
                EqualTermsAreAlphaEquilvalent'(t1'',t2'',id1,id2);
            }
}


lemma SubstAlphaEquivalence (t:LambdaTerm,x:Id,x':Id)
    requires !(x' in vars(t))
    ensures alphaEquivalence(Lambda(x,t),Lambda(x',substitution(t,x,Var(x'))))
{
    assert []+[x]==[x] && []+[x']==[x'];
    SubstAlphaEquivalence'(t, x, x',substitution(t,x,Var(x')), [x], [x']);
}


lemma SubstAlphaEquivalence'(t:LambdaTerm, x:Id, x':Id,t2:LambdaTerm, id1:seq<Id>, id2:seq<Id>)
    requires |id1| == |id2| >0
    requires !(x' in vars(t))
    requires id1[0]==x && id2[0]==x'
    requires forall i :: 0 <= i < |id1| ==>
        (id1[i] == x <==> id2[i] == x') &&
        (id1[i] != x ==> id1[i] == id2[i])
    requires t2==substitution(t,x,Var(x'))
    ensures alphaEquivalence'(t, t2, id1, id2)
    decreases lHeight(t)
{
    match t 
        case Application(t1a,t1b) =>
        {
            var t2a:=substitution(t1a,x,Var(x'));
            var t2b:=substitution(t1b,x,Var(x'));
            assert t2==Application(t2a,t2b);

            SubstAlphaEquivalence'(t1a,x,x',t2a,id1,id2);
            SubstAlphaEquivalence'(t1b,x,x',t2b,id1,id2);

            assert alphaEquivalence'(t1a,t2a,id1,id2);
            assert alphaEquivalence'(t1b,t2b,id1,id2);

            assert alphaEquivalence'(t,t2,id1,id2);
        }
        case Lambda(z,t1') =>
        {
            if z==x
            {
                assert t2==t;
                var id1' := id1+[x] ;
                var id2' := id2+[x] ;
                

                forall y | y in vars(t1') ensures findId(id1', y) == findId(id2', y) {
                    if y != x {
                        assert y in vars(t);
                        assert y != x'; 
                    }
                }
                EqualTermsAreAlphaEquilvalent'(t1',t1',id1',id2');
                assert alphaEquivalence'(t, t2, id1, id2);
            }
            else 
            {
                
                var t2' := substitution(t1', x, Var(x'));
                assert t2 == Lambda(z, t2');

                var id1':=id1+[z];
                var id2':=id2+[z];

                SubstAlphaEquivalence'(t1',x,x',t2',id1',id2');

                assert alphaEquivalence'(t1',t2',id1',id2');
            }
        }
        case Var(z) =>
        {
            if (z==x)
            {
                assert t2==Var(x');
                var r1:=findId(id1,x);
                var r2:=findId(id2,x');
                assert r1!=None;
                
                assert r1==r2;
            }
            else 
            {
                assert t2==t;
                assert z!=x';
            }
        }
}


lemma LambdaEquivalence(t1:LambdaTerm,t2:LambdaTerm,x1:Id,x2:Id)
    requires alphaEquivalence(t1,t2)
    requires !(x1 in free(t1)) && !(x2 in free(t2))
    ensures alphaEquivalence(Lambda(x1,t1),Lambda(x2,t2))
{
    LambdaEquivalence'(t1,t2,x1,x2,[],[]);
    assert [x1]==[x1]+[] && [x2]==[x2]+[];
    assert alphaEquivalence'(t1,t2,[x1],[x2]);
    assert [x1]==[]+[x1] && [x2]==[]+[x2];
}



lemma LambdaEquivalence'(t1:LambdaTerm,t2:LambdaTerm,x1:Id,x2:Id,id1:seq<Id>,id2:seq<Id>)
    requires alphaEquivalence'(t1,t2,id1,id2)
    requires x1 in free(t1) ==> x1 in id1  
    requires x2 in free(t2) ==> x2 in id2
    ensures alphaEquivalence'(t1,t2,[x1]+id1,[x2]+id2)
{
    match t1 
        case Var(x) =>
        {
            var y: Id :| t2 == Var(y);
            var r1 := findId(id1, x);
            var r2 := findId(id2, y);
            
            var id1' := [x1] + id1;
            var id2' := [x2] + id2;
            var r1' := findId(id1', x);
            var r2' := findId(id2', y);

            findId_prepend(id1, x, x1);
            findId_prepend(id2, y, x2);

            if r1 == None
            {
                assert x==y;
                
                assert x!=x1; 
                
                assert y!=x2;

                assert !(x in id1');
                assert !(y in id2');

                assert r1'==None;
                assert r2'==None;
            }
            else 
            {
                var i1 :|r1==Some(i1);
                assert r2==Some(i1); 

                var new_pos:=i1+1;

                assert id1'[new_pos]==x;
                
             

                
                assert r1'==Some(new_pos);

                assert id2'[new_pos]==y;

                assert r2' == Some(new_pos);
    }
        }
        case Lambda(x,t1')=>
        {
            var y:nat,t2':LambdaTerm:|t2==Lambda(y,t2');
            var id1':=id1+[x];
            var id2':=id2+[y];
            LambdaEquivalence'(t1',t2',x1,x2,id1',id2');
            assert [x1]+id1+[x]==[x1]+id1';
            assert [x2]+id2+[y]==[x2]+id2';

        }
        case Application(t1a,t1b)=>
        {
            var t2a:LambdaTerm,t2b:LambdaTerm:|t2==Application(t2a,t2b);
            LambdaEquivalence'(t1a,t2a,x1,x2,id1,id2);
            LambdaEquivalence'(t1b,t2b,x1,x2,id1,id2);

        }
}


lemma AlphaCongruenceLambda(y:Id, t1:LambdaTerm, t2:LambdaTerm)
    requires alphaEquivalence(t1, t2)
    ensures alphaEquivalence(Lambda(y, t1), Lambda(y, t2))
{
    assert []+[y]==[y]==[y]+[];
    AlphaCongruenceLambda'( t1, t2,y, [], []);
}

lemma AlphaCongruenceLambda'(t1:LambdaTerm, t2:LambdaTerm,y:Id, id1:seq<Id>, id2:seq<Id>)
    requires alphaEquivalence'(t1, t2, id1, id2)
    ensures alphaEquivalence'(t1, t2, [y]+id1, [y]+id2)
    decreases minim(lHeight(t1), lHeight(t2))
{
    match t1 {
        case Var(x) => {
            var z :| t2 == Var(z);
            var r1:=findId(id1, x);
            var r2:=findId(id2, z);
            
            var id1':=[y]+id1;
            var id2':=[y]+id2;
            var r1':=findId(id1', x);
            var r2':=findId(id2', z);

            findId_prepend(id1, x, x);
            findId_prepend(id2, y, x);

            if r1 == None {
                assert x == z;
                if x == y {
                    assert id1'[0] == x;
                    assert r1' == Some(0);

                    assert id2'[0] == z;
                    assert r2' == Some(0);

                } else {
                    assert r1' == None;
                    assert r2' == None;
                }
            } else {
                var i1 :| r1 == Some(i1);
                var new_pos := i1 + 1;

                assert id1'[new_pos] == x;
                assert r1' == Some(new_pos);

                assert id2'[new_pos] == z;
                assert r2' == Some(new_pos);
            }
        }
        case Lambda(x, t1') => {
            var z, t2' :| t2 == Lambda(z, t2');
            AlphaCongruenceLambda'( t1', t2',y, id1+[x], id2+[z]);
            assert [y]+id1+[x] == [y] + (id1+[x]);
            assert [y]+id2+[z] == [y] + (id2+[z]);
        }
        case Application(t1a, t1b) => {
            var t2a, t2b :| t2 == Application(t2a, t2b);
            AlphaCongruenceLambda'( t1a, t2a,y, id1, id2);
            AlphaCongruenceLambda'( t1b, t2b,y, id1, id2);
        }
    }
}




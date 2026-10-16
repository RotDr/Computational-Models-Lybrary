include "../AlphaEquivalence.dfy"
datatype RefLambdaTerm = RefLambda(t':RefLambdaTerm) | FreeVar(x:Id) | BoundVar(n:nat) | App(t1:RefLambdaTerm,t2:RefLambdaTerm)
predicate locallyClosed(t:RefLambdaTerm)
{
    locallyClosed'(t,0)
}
predicate locallyClosed'(t:RefLambdaTerm,l_count:nat)
{
    match t 
        case FreeVar(_)=> true 
        case BoundVar(ref)=> ref<l_count
        case RefLambda(t')=> locallyClosed'(t',l_count+1)
        case App(t1,t2)=> locallyClosed'(t1,l_count) && locallyClosed'(t2,l_count)
}
ghost predicate locallyClosedCanon(t:RefLambdaTerm)
    decreases refLHeight(t)
{
        match t 
        case FreeVar(_)=> true 
        case BoundVar(ref)=> false 
        case RefLambda(t')=>  
        assert forall x:Id:: refLHeight(open'(0,x,t'))==refLHeight(t');
        (exists L:seq<Id>::allUnique(L) && forall x:Id:: !(x in L) ==> locallyClosedCanon(open'(0,x,t')))
        case App(t1,t2)=> locallyClosedCanon(t1) && locallyClosedCanon(t2)
}

lemma LocalClosingEquivalence1(t:RefLambdaTerm)
    requires locallyClosedCanon(t)
    decreases refLHeight(t)
    ensures locallyClosed(t)
{
    match t 
        case FreeVar(_)=>{}
        case App(t1,t2)=>{
            LocalClosingEquivalence1(t1);
            LocalClosingEquivalence1(t2);
        }
        case RefLambda(t')=>
        {
            var L:seq<Id>:|allUnique(L) && forall x:Id:: !(x in L) ==> locallyClosedCanon(open'(0,x,t'));

            var x:Id:=addAnUniqueId(L)[0]; 
            assert locallyClosed(open'(0,x,t'));
            LocalClosingEquivalence1(open'(0,x,t'));
            BodyUp(t',x);

        }
}
lemma LocalClosingEquivalence2(t:RefLambdaTerm)
    requires locallyClosed(t)
    decreases refLHeight(t)
    ensures locallyClosedCanon(t)
{
    match t 
        case FreeVar(_)=>{}
        case App(t1,t2)=>{
            LocalClosingEquivalence2(t1);
            LocalClosingEquivalence2(t2);
        }
        case BoundVar(_)=>{}
        case RefLambda(t')=>
        {
            var L:seq<Id>:=freeVarsSeq(t);
            forall x:Id| !(x in L)
                ensures locallyClosedCanon(open'(0,x,t'))
            {    
                IfWeForgetThatIsOpenedItThenIsClosed(t,x);
                LocalClosingEquivalence2(open'(0,x,t'));
            }
        }
}

lemma BodyUp(t:RefLambdaTerm,x:Id)
    requires locallyClosed(open'(0,x,t))
    ensures locallyClosed(RefLambda(t))
{
    
    BodyUp'(t,x,0);
}

lemma BodyUp'(t:RefLambdaTerm,x:Id,depth:nat)
    requires locallyClosed'(open'(depth,x,t),depth)
    ensures locallyClosed'(t,depth+1)
{
    match t 
        case BoundVar(ref_id) => 
        {
            if (ref_id!=depth)
            {
                assert open'(depth,x,t)==t;
            }
        }
        case RefLambda(t')=>{
            BodyUp'(t',x,depth+1);
        }
        case App(t1,t2)=>{
            BodyUp'(t1,x,depth);
            BodyUp'(t2,x,depth);
        }
        case FreeVar(y)=>
        {

        }
}
predicate body(t:RefLambdaTerm)
{
    locallyClosed'(t,1)
}
function refLHeight(t:RefLambdaTerm) :nat
{
    match t 
        case FreeVar(_)=> 1
        case BoundVar(ref)=> 1
        case RefLambda(t')=> 1+refLHeight(t')
        case App(t1,t2)=> 1+refLHeight(t1) + refLHeight(t2)
}
predicate isRefReadyForNegativeShift(t:RefLambdaTerm,bytes:nat)
{
    isRefReadyForNegativeShift'(t,0,bytes)
}
predicate isRefReadyForNegativeShift'(t:RefLambdaTerm,l_count:nat,bytes:nat)
{
    match t 
        case FreeVar(_)=> true 
        case BoundVar(ref)=> ref<l_count || ref>=l_count+bytes 
        case RefLambda(t')=> isRefReadyForNegativeShift'(t',l_count+1, bytes)
        case App(t1,t2)=> isRefReadyForNegativeShift'(t1,l_count,bytes) && isRefReadyForNegativeShift'(t2,l_count,bytes)
}


predicate refAlpha(t1:RefLambdaTerm,t2:RefLambdaTerm)
{
    t1==t2
}


function fromLambdaToRef (t:LambdaTerm) : RefLambdaTerm
  
{
    fromLambdaToRef'(t,[])
}
function fromLambdaToRef'(t:LambdaTerm,ids:seq<Id>): RefLambdaTerm

{
    match t 
        case Lambda(x,t') => RefLambda(fromLambdaToRef'(t',ids+[x]))
        case Var(x) =>(  match findId(ids,x)
                            case None=> FreeVar(x)
                            case Some(refId) => BoundVar(refId)
        )
        case Application(t1,t2) => App(fromLambdaToRef'(t1,ids),fromLambdaToRef'(t2,ids))
                               
}


lemma FromLambdaToRefIsValid(t:LambdaTerm)
    ensures locallyClosed(fromLambdaToRef(t))
{
    FromLambdaToRefIsValid'(t,[],0);
}

lemma FromLambdaToRefIsValid'(t:LambdaTerm,ids:seq<Id>,l_count:nat)
    requires l_count==|ids|
    ensures locallyClosed'(fromLambdaToRef'(t,ids),l_count)
{

}


function freeVarsSeq(t:RefLambdaTerm):seq<Id>
    ensures allUnique(freeVarsSeq(t))
{
    match t 
        case RefLambda(t') => freeVarsSeq(t')
        case App(t1,t2) => reunion(freeVarsSeq(t1),freeVarsSeq(t2))
        case FreeVar(x) => [x]
        case BoundVar(ref) => []
}



function fromRefToLambda(t:RefLambdaTerm): LambdaTerm
    requires locallyClosed(t)
{
    fromRefToLambda'(t,freeVarsSeq(t),[])
}
function fromRefToLambda'(t:RefLambdaTerm,ids:seq<Id>,lambda_names:seq<Id>):LambdaTerm
    requires allUnique(ids)
    requires allUnique(lambda_names)
    requires forall id:Id::id in ids ==>!(id in lambda_names)
    requires locallyClosed'(t,|lambda_names|)
{
    match t 
        case RefLambda(t') => (
            var new_id:=addAnUniqueId(reunion(ids,lambda_names))[0];
            Lambda(new_id,fromRefToLambda'(t',ids,lambda_names+[new_id]))
        )
        case App(t1,t2)=>(
            Application(fromRefToLambda'(t1,ids,lambda_names),fromRefToLambda'(t2,ids,lambda_names))
        )
        case FreeVar(x)=> Var(x)
        case BoundVar(ref) =>(
             Var(lambda_names[ref]) )
}



predicate isAbstraction(t:RefLambdaTerm)
{
    match t 
        case RefLambda(_) => true 
        case _ => false 
}

function open(t:RefLambdaTerm): (RefLambdaTerm,Id)
    // requires isAbstraction(t)
    // ensures locallyClosed(open(t).t)
    ensures var (t',_):=open(t);
    refLHeight(t)==refLHeight(t')
{
    var ids:=freeVarsSeq(t);
    var new_id:=addAnUniqueId(ids)[0];
    assert !(new_id in ids);
    (open'(0,new_id,t),new_id)
}
function open'(depth:nat,new_id:Id,t:RefLambdaTerm) :RefLambdaTerm
    // requires locallyClosed'(t,depth)
    decreases t
    ensures var t':=open'(depth,new_id,t);
    refLHeight(t)==refLHeight(t')
    // ensures locallyClosed'(open'(depth,new_id,t),depth-1)
{
    match t 
        case FreeVar(_) => t 
        case BoundVar(x) => if depth==x then 
        // assert locallyClosed'(FreeVar(new_id),depth-1);
        FreeVar(new_id) else BoundVar(x) 
        case RefLambda(t')=> RefLambda(open'(depth+1,new_id,t'))
        case App(t1,t2) =>  App(open'(depth,new_id,t1),open'(depth,new_id,t2))
}


function close (opened_t:RefLambdaTerm,opened_id:Id):RefLambdaTerm

{
    close'(opened_t,opened_id,0)
}

function close'(t:RefLambdaTerm,x:Id,depth:nat):RefLambdaTerm
{
    match t 
    case FreeVar(y) => if  x==y then BoundVar(depth) else t 
    case BoundVar(_) => t 
    case App(t1,t2)=> App (close'(t1,x,depth),close'(t2,x,depth))
    case RefLambda(t')=> RefLambda(close'(t',x,depth+1))
    
}

lemma OpenClose(t:RefLambdaTerm,x:Id)
    requires locallyClosed(t)
    ensures open'(0,x,close(t,x))==t
{
    OpenClose'(t,x,0);
    assert open'(0,x,close'(t,x,0))==t;
}
lemma OpenClose'(t:RefLambdaTerm,x:Id,depth:nat)
    requires locallyClosed'(t,depth)
    ensures open'(depth,x,close'(t,x,depth))==t
{

}

lemma CloseOpen(t:RefLambdaTerm,x:Id)
    requires !(x in freeVarsSeq(t))
    ensures close(open'(0,x,t),x)==t
{
    CloseOpen'(t,x,0);
}

lemma CloseOpen'(t:RefLambdaTerm,x:Id,depth:nat)
    requires !(x in freeVarsSeq(t))
    ensures close'(open'(depth,x,t),x,depth)==t
{
    
}


function opening (t:RefLambdaTerm,l_count:nat,t':RefLambdaTerm): RefLambdaTerm

{
    match t 
        case FreeVar(_) =>t 
        case BoundVar(ref) => if ref==l_count then t' 
                                    else if ref>l_count then BoundVar(ref)
                                        else t
        case App(t1,t2) => App(
            opening(t1,l_count,t'),
            opening(t2,l_count,t')
        )
        case RefLambda(t1)=>RefLambda(opening(t1,l_count+1,t'))

}

function LNSubstitution(t:RefLambdaTerm,x:Id,t':RefLambdaTerm):RefLambdaTerm 
{
    match t 
        case FreeVar(y) => if y==x then t' else t
        case BoundVar(_) => t
        case App(t1,t2) => App(
            LNSubstitution(t1,x,t'),
            LNSubstitution(t2,x,t')
        )
        case RefLambda(t1)=>RefLambda(LNSubstitution(t1,x,t'))
}


predicate isRefAppLambda(t:RefLambdaTerm)
{
    match t 
        case App(t1,t2) => (match t1 
                                case RefLambda(_) => true 
                                case _=> false )
        case _=> false
}

function numberOfRedexes(t:RefLambdaTerm):nat 
{
    match t 
        case FreeVar(_)=> 0
        case BoundVar(_)=> 0
        case RefLambda(t')=>numberOfRedexes(t')
        case App(t1,t2) => if isRefAppLambda(t) then 1+numberOfRedexes(t1)+numberOfRedexes(t2) 
                                else numberOfRedexes(t1)+numberOfRedexes(t2)
}

lemma RefNoVariableToReplace(t:RefLambdaTerm,x:Id,t':RefLambdaTerm)
    requires !(x in freeVarsSeq(t))
    ensures LNSubstitution(t,x,t')==t
{

}
lemma RefSubsitutionClosure(t:RefLambdaTerm,x:Id,t':RefLambdaTerm)
    requires locallyClosed(t) 
    requires locallyClosed(t')
    ensures locallyClosed(LNSubstitution(t,x,t'))
{
    RefSubsitutionClosure'(t,x,t',0);
}
lemma RefSubsitutionBody(t:RefLambdaTerm,x:Id,t':RefLambdaTerm)
    requires body(t)
    requires locallyClosed(t')
    ensures body(LNSubstitution(t,x,t'))
{
    RefSubsitutionBody'(t,x,t',0);
}

lemma RefSubsitutionBody'(t:RefLambdaTerm,x:Id,t':RefLambdaTerm,depth:nat)
    requires locallyClosed'(t,depth+1)
    requires locallyClosed'(t',depth)
    ensures locallyClosed'(LNSubstitution(t,x,t'),depth+1)
{
    match t 
        case FreeVar(y) => if (x==y) 
        {
            assert locallyClosed'(t',depth);
            LocallyClosedAtDifferentLevels(t',depth,depth+1);
        }
        else {
            LocallyClosedAtDifferentLevels(t',depth,depth+1);

        }
        case BoundVar(_) => {}
        case RefLambda(t_prim)=>
        {
            var sub_t':=LNSubstitution(t_prim,x,t');
            LocallyClosedAtDifferentLevels(t',depth,depth+1);
            assert locallyClosed'(t',depth+1);
            RefSubsitutionBody'(t_prim,x,t',depth+1);
        }
        case App(t1,t2) =>
        {
            RefSubsitutionBody'(t1,x,t',depth);
            RefSubsitutionBody'(t2,x,t',depth);
        }
}
lemma LocallyClosedAtDifferentLevels(t:RefLambdaTerm,x:nat,y:nat)
    requires locallyClosed'(t,x)
    requires x<y 
    ensures locallyClosed'(t,y)
{

}

lemma OpeningIsClosed(t:RefLambdaTerm,x:Id)
    requires locallyClosed(RefLambda(t))
    ensures locallyClosed(open'(0,x,t));

{
    OpeningIsClosed'(t,x,0);

}
lemma OpeningIsClosed'(t:RefLambdaTerm,x:Id,depth:nat)
    requires locallyClosed'(t,depth+1)
    ensures locallyClosed'(open'(depth,x,t),depth);

{
    match t 
        case FreeVar(_)=>{}
        case BoundVar(ref_id)=>{
            if (ref_id==depth)
            {
                assert open'(depth,x,t)==FreeVar(x);
            }
            else
            {

            }
        }
        case RefLambda(t')=>
        {
            OpeningIsClosed'(t',x,depth+1);
        }
        case App(t1,t2)=>
        {
            OpeningIsClosed'(t1,x,depth);
            OpeningIsClosed'(t1,x,depth);
        }
    
}
lemma RefSubsitutionClosure'(t:RefLambdaTerm,x:Id,t':RefLambdaTerm,depth:nat)
    requires locallyClosed'(t,depth) 
    requires locallyClosed'(t',depth)
    ensures locallyClosed'(LNSubstitution(t,x,t'),depth)
{
    match t 
        case FreeVar(y) => if (x==y) 
        {
            assert locallyClosed'(t',depth);
        }
        else {

        }
        case BoundVar(_) => {}
        case RefLambda(t_prim)=>
        {
            var sub_t':=LNSubstitution(t_prim,x,t');
            LocallyClosedAtDifferentLevels(t',depth,depth+1);
            assert locallyClosed'(t',depth+1);
            RefSubsitutionClosure'(t_prim,x,t',depth+1);
        }
        case App(t1,t2) =>
        {
            RefSubsitutionClosure'(t1,x,t',depth);
            RefSubsitutionClosure'(t2,x,t',depth);
        }
}

lemma OpeningMaintainsNumberOfRedexes(t:RefLambdaTerm)
    ensures var (opened_t,_):=open(t);
    numberOfRedexes(t)==numberOfRedexes(opened_t)
{
    var ids:=freeVarsSeq(t);
    var new_id:=addAnUniqueId(ids)[0];
    OpeningMaintainsNumberOfRedexes'(t,new_id,0);
}
lemma OpeningMaintainsNumberOfRedexes'(t:RefLambdaTerm,new_id:Id,depth:nat)
    ensures var opened_t:=open'(depth,new_id,t);
    numberOfRedexes(t)==numberOfRedexes(opened_t)
{
    var opened_t:=open'(depth,new_id,t);
    match t 
        case FreeVar(x) =>
        {
            assert t==opened_t;
        }
        case BoundVar(ref_id) =>
        {
            if (ref_id==depth)
            {
                assert opened_t==FreeVar(new_id);
                assert numberOfRedexes(opened_t)==0;
            }
            else 
            {
                assert t==opened_t;
            }
        }
        case App(t1,t2) =>
        {
            OpeningMaintainsNumberOfRedexes'(t2,new_id,depth);
            OpeningMaintainsNumberOfRedexes'(t1,new_id,depth);

            if isRefAppLambda(t) 
            {
                assert isRefAppLambda(opened_t);
            }
        }
        case  RefLambda(t')=>
        {
            OpeningMaintainsNumberOfRedexes'(t',new_id,depth+1);
        }
}
lemma LocallyClosedIsNotOpened(t:RefLambdaTerm)
    requires locallyClosed(t) 
    ensures var (t',_):=open(t); t'==t
{
    var ids:=freeVarsSeq(t);
    var new_id:=addAnUniqueId(ids)[0];
    LocallyClosedIsNotOpened'(t,0,new_id);
}
lemma LocallyClosedIsNotOpened'(t:RefLambdaTerm,depth:nat,new_id:Id)
    requires locallyClosed'(t,depth) 
    ensures t==open'(depth,new_id,t)
{

}

lemma LocallyClosedIsNotOpening(t:RefLambdaTerm,depth:nat,t':RefLambdaTerm)
    requires locallyClosed'(t,depth) 
    ensures t==opening(t,depth,t')
{

}
lemma SubstitutionAndOpening(t:RefLambdaTerm,x:Id,y:Id,t':RefLambdaTerm,depth:nat)
    requires locallyClosed'(t',depth)
    requires x!=y 
    ensures LNSubstitution(open'(depth,y,t),x,t')==open'(depth,y,LNSubstitution(t,x,t'))
{
    match t 
        case FreeVar(id)=>
        {
            assert open'(depth,y,t)==t;
            if (id==x)
            {
                assert LNSubstitution(open'(depth,y,t),x,t')==t';
                assert LNSubstitution(t,x,t')==t';
                LocallyClosedIsNotOpened'(t',depth,y);
                assert open'(depth,y,LNSubstitution(t,x,t'))==t';
            }
            else 
            {
                assert LNSubstitution(open'(depth,y,t),x,t')==t; 
                assert LNSubstitution(t,x,t')==t;
                assert open'(depth,y,LNSubstitution(t,x,t'))==t;
            }
        }
        case BoundVar(ref_id)=>
        {
            if (ref_id==depth) 
            {
                assert open'(depth,y,t)==FreeVar(y);
                assert x!=y; 
                assert LNSubstitution(open'(depth,y,t),x,t')==FreeVar(y);
                assert LNSubstitution(t,x,t')==t;
                assert open'(depth,y,LNSubstitution(t,x,t'))==FreeVar(y);
                
            }
            else 
            {
                assert open'(depth,y,t)==t;
                assert LNSubstitution(t,x,t')==t;
            }
        }
        case RefLambda(t_prim)=>
        {
            LocallyClosedAtDifferentLevels(t',depth,depth+1);
            SubstitutionAndOpening(t_prim,x,y,t',depth+1);
        }
        case App(t1,t2)=>
        {
            SubstitutionAndOpening(t1,x,y,t',depth);
            SubstitutionAndOpening(t2,x,y,t',depth);
        }
}

function refBetaReduction(t:RefLambdaTerm) : RefLambdaTerm
    requires isRefAppLambda(t)
    
{
    match t 
        case App(t1,t2) => (match t1
                                case RefLambda(t1') => opening(t1',0,t2)
        )
}

function refBetaReductionStep(t:RefLambdaTerm,choice:nat):RefLambdaTerm
    requires numberOfRedexes(t)>choice 
    decreases refLHeight(t)
{
    match t 
        case App(t1,t2) => (
            var n1:=numberOfRedexes(t1);
            var n2:=numberOfRedexes(t2);
            if isRefAppLambda(t) then 
            (
                if choice==0 then 
                    refBetaReduction(t)
                else 
                    if (choice<=n1) then 
                        App(refBetaReductionStep(t1,choice-1),t2)
                    else 
                        assert choice>n1;
                        assert choice<numberOfRedexes(t);
                        assert n2+n1+1==numberOfRedexes(t); 
                        App(t1,refBetaReductionStep(t2,choice-1-n1))
            )
            else 
            (
                if (choice<n1) then 
                        App(refBetaReductionStep(t1,choice),t2)
                    else 
                        assert choice>=n1;
                        assert choice<numberOfRedexes(t);
                        assert n2+n1==numberOfRedexes(t); 
                        App(t1,refBetaReductionStep(t2,choice-n1))
            )
            )
        case RefLambda(t')=>
        (
            var (opened_t',x):=open(t');
            assert refLHeight(t')<refLHeight(t);
            assert refLHeight(t')==refLHeight(opened_t');
            OpeningMaintainsNumberOfRedexes(t');
            close(refBetaReductionStep(opened_t',choice),x)
        ) 

}

lemma SubstitutionIntro(t:RefLambdaTerm,x:Id,t':RefLambdaTerm,depth:nat)
    requires !(x in freeVarsSeq(t))
    ensures opening(t,depth,t')==LNSubstitution(open'(depth,x,t),x,t')
{
    match t 
        case FreeVar(y)=>
        {
            assert y in freeVarsSeq(t); 
            assert !(x in freeVarsSeq(t));
            assert x!=y;
        }
        case BoundVar(ref_id)=>
        {
            if (ref_id==depth)
            {
                assert opening(t,depth,t')==t';
                assert open'(depth,x,t)==FreeVar(x);
            }
            else 
            {
                assert opening(t,depth,t')==t;
                assert open'(depth,x,t)==t;
            }
        }   
        case App(t1,t2)=>
        {
            SubstitutionIntro(t1,x,t',depth);
            SubstitutionIntro(t2,x,t',depth);
        }
        case RefLambda(t_prim)=>
        {
            SubstitutionIntro(t_prim,x,t',depth+1);
        }

}

lemma SubstitutionOpen(t:RefLambdaTerm,x:Id,u:RefLambdaTerm,v:RefLambdaTerm,depth:nat)
    requires locallyClosed'(u,depth)
    ensures LNSubstitution(opening(t,depth,v),x,u)==opening(LNSubstitution(t,x,u),depth,LNSubstitution(v,x,u))
{
    match t 
        case FreeVar(y)=>
        {
            assert opening(t,depth,v)==t;
            if (x==y)
            {
                assert LNSubstitution(t,x,u)==u;
                LocallyClosedIsNotOpening(u,depth,LNSubstitution(v,x,u));
                assert opening(LNSubstitution(t,x,u),depth,LNSubstitution(v,x,u))==u;

            }
            else 
            {

            }
        }
        case BoundVar(ref_id)=>
        {

            
        }
        case RefLambda(t')=>{
            LocallyClosedAtDifferentLevels(u,depth,depth+1);
            SubstitutionOpen(t',x,u,v,depth+1);
        }
        case App(t1,t2)=>{
            SubstitutionOpen(t1,x,u,v,depth);
            SubstitutionOpen(t2,x,u,v,depth);
        }
}

lemma NotFoundInFreeAfterOpening(t:RefLambdaTerm,x:Id,depth:nat)
    requires !(x in freeVarsSeq(t))
    requires !(x in freeVarsSeq(open'(depth,x,t)))
    ensures open'(depth,x,t)==t
{

}

lemma NoChangesOccuredWhenOpening(t:RefLambdaTerm,x:Id,y:Id,depth:nat)
    requires open'(depth,x,t)==t 
    ensures open'(depth,y,t)==t
{

}

lemma OpenCommutes(t: RefLambdaTerm, depth1: nat, x1: Id, depth2: nat, x2: Id)
    requires depth1 != depth2
    requires x1 != x2
    ensures open'(depth1, x1, open'(depth2, x2, t)) == open'(depth2, x2, open'(depth1, x1, t))
{
    match t
        case FreeVar(_) => {}
        case BoundVar(ref) => {}
        case RefLambda(t') => { OpenCommutes(t', depth1+1, x1, depth2+1, x2); }
        case App(t1, t2) => { OpenCommutes(t1, depth1, x1, depth2, x2); OpenCommutes(t2, depth1, x1, depth2, x2); }
}

lemma NotInFreeVarsOpen(t: RefLambdaTerm, depth: nat, x: Id, y: Id)
    requires x != y
    requires !(y in freeVarsSeq(t))
    ensures !(y in freeVarsSeq(open'(depth, x, t)))
{
    match t
        case FreeVar(_) => {}
        case BoundVar(ref) => {}
        case RefLambda(t') => { NotInFreeVarsOpen(t', depth+1, x, y); }
        case App(t1, t2) => { NotInFreeVarsOpen(t1, depth, x, y); NotInFreeVarsOpen(t2, depth, x, y); }
}

lemma IfWeForgetThatIsOpenedItThenIsClosed(t:RefLambdaTerm,x:Id)
    requires locallyClosed(t)
    requires (match t 
                case RefLambda(_)=>true
                case _=> false)
    ensures (match t 
                case RefLambda(t')=>locallyClosed(open'(0,x,t')))
     
{
    match t
        case RefLambda(t')=>
    IfWeForgetThatIsOpenedItThenIsClosed'(t',x,1);
}

lemma IfWeForgetThatIsOpenedItThenIsClosed'(t:RefLambdaTerm,x:Id,depth:nat)
    requires depth>=1
    requires locallyClosed'(t,depth)
    ensures locallyClosed'(open'(depth-1,x,t),depth-1)
{
    match t 
        case FreeVar(_) => {}
        case BoundVar(ref_id)=>
        {
            if (ref_id==depth-1)
            {
                assert open'(depth-1,x,t)==FreeVar(x);
            }
            else
            {
                assert ref_id<depth-1;
            }
        }
        case App(t1,t2)=>
        {
            IfWeForgetThatIsOpenedItThenIsClosed'(t1,x,depth);
            IfWeForgetThatIsOpenedItThenIsClosed'(t2,x,depth);
        }
        case RefLambda(t')=>
        {
            IfWeForgetThatIsOpenedItThenIsClosed'(t',x,depth+1);
        }
}
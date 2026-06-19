include "./../objects.dfy"

predicate isTrue(t:LambdaTerm) 
{
    match t 
        case Lambda(x,Lambda(y,Var(z))) => z==x
        case _ => false
}
function trueVar(x:Id,y:Id) : LambdaTerm
    ensures isTrue(trueVar(x,y))
{
    Lambda(x,Lambda(y,Var(x)))
}
function trueVal():LambdaTerm
    ensures isTrue(trueVal())
{
        trueVar(0,1)
}


predicate isFalse(t:LambdaTerm) 
{
    match t 
        case Lambda(x,Lambda(y,Var(z))) => z==y
        case _ => false
}
function falseVar(x:Id,y:Id):LambdaTerm
    ensures isFalse(falseVar(x,y))
{
    Lambda(x,Lambda(y,Var(y)))
}
function falseVal():LambdaTerm
    ensures isFalse(falseVal())
{
    falseVar(0,1)
}


predicate isAnd(t:LambdaTerm) //sintactic
{
    match t 
        case Lambda(x,Lambda(y,Application(Application(Var(id1),Var(id2)),Var(id3)))) => id1==x==id3 && id2==y
        case _ => false
}
function andVar(x:Id,y:Id) : LambdaTerm
    ensures isAnd(andVar(x,y))
{
    Lambda(x,Lambda(y,Application(Application(Var(x),Var(y)),Var(x))))
}
function andVal():LambdaTerm
    ensures isAnd(andVal())
{
    andVar(0,1)
}


predicate isOr(t:LambdaTerm)
{
    match t 
        case Lambda(x,Lambda(y,Application(Application(Var(id1),Var(id2)),Var(id3)))) => id1==x==id2 && id3==y
        case _ => false
}
function orVar(x:Id,y:Id) :LambdaTerm
    ensures isOr(orVar(x,y))
{
    Lambda(x,Lambda(y,Application(Application(Var(x),Var(x)),Var(y))))
}
function orVal():LambdaTerm
    ensures isOr(orVal())
{
    orVar(0,1)
}


predicate isNot(t:LambdaTerm)
{
    match t 
        case Lambda(x,Application(Application(Var(y),t1),t2)) => isFalse(t1) && isTrue(t2) && x==y
        case _ => false
}
function notVar(fals:LambdaTerm,tru:LambdaTerm,id:Id) : LambdaTerm
    requires isFalse(fals)
    requires isTrue(tru)
{
    Lambda(id,Application(Application(Var(id),fals),tru)) 
}
function notVal() : LambdaTerm
{
    Lambda(1,Application(Application(Var(1),falseVal()),trueVal()))
}

predicate isZero(t:LambdaTerm)
{
    isFalse(t)
}


function fromNumberToLambdaVar(nr:nat,f:Id,x:Id) : LambdaTerm
    ensures isTermThatNumber(fromNumberToLambdaVar(nr,f,x),nr)
{
    Lambda(f,Lambda(x,nFsAndOneX(nr,x,f)))
}

function fromNumberToLambdaVal(nr:nat): LambdaTerm
    ensures isTermThatNumber(fromNumberToLambdaVal(nr),nr)
{
    fromNumberToLambdaVar(nr,2,0)
}
function nFsAndOneX(n:nat,x:Id,f:Id) :LambdaTerm
    decreases n
{
    if n==0 then Var(x)
    else Application(Var(f),nFsAndOneX(n-1,x,f))
}

predicate isTermThatNumber(t:LambdaTerm,n:nat)

{
    match t 
        case Lambda(f,Lambda(x,t')) => t'==nFsAndOneX(n,x,f)
        case _ => false
}

ghost predicate isTermANumber(t:LambdaTerm)
{
    exists n:nat:: isTermThatNumber(t,n)
}

predicate isSucc(t:LambdaTerm)
{
    match t 
        case Lambda(n,
                    Lambda(f,
                        Lambda(x,
                            Application(
                                Application(Var(id1),Var(id2)),
                                Application(Var(id3),Var(id4))
                                        )
                                )
                        )
                    ) => id1==n && id2==id3==f && id4==x 
        case _ => false
}

function succVar(n:Id,f:Id,x:Id):LambdaTerm
    ensures isSucc(succVar(n,f,x))
{
    Lambda(n,
            Lambda(f,
                Lambda(x,
                    Application(
                        Application(Var(n),Var(f)),
                        Application(Var(f),Var(x))
                                )
                        )
                )
            )
}

function succVal():LambdaTerm
    ensures isSucc(succVal())
{
    succVar(3,2,0)
}


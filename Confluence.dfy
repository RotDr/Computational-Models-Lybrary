include "Lambda.dfy"
include "BetaReduction.dfy"


ghost predicate parallelReduction(t1:LambdaTerm,t2:LambdaTerm)
    decreases lHeight(t1)
{
    match t1 
            case Application(t1a,t1b) =>( match t2 
                                        case Application(t2a,t2b) => parallelReduction(t1a,t2a) && parallelReduction(t1b,t2b)
                                        case _ => false
            ) ||
            ( match t1a 
                    case Lambda(x,M) => ( 
                     exists M': LambdaTerm, N': LambdaTerm ::
              assert lHeight(M)<lHeight(t1);       
              parallelReduction(M, M')          
              && parallelReduction(t1b, N')    
              && t2 == substitution(M', x, N') 
                    )
                    case _=> t1==t2 
            ) 
            case Lambda(x,t1a) => (
                ( match t2 
                                        case Lambda(y,t2a)=> x==y && parallelReduction(t1a,t2a)
                                        case _ => false
            )
            )
            case _ => t1==t2
}

lemma parallelReductionIsReflexive (t:LambdaTerm)
    ensures parallelReduction(t,t)
{

}


// lemma SubstitutionLemma (M:LambdaTerm,N:LambdaTerm,P:LambdaTerm,x:Id,y:Id)
//     requires x!=y
//     requires !(x in free(P))
//     ensures caSubstitution(caSubstitution(M,x,N),y,P)==caSubstitution(caSubstitution(M,y,P),x,caSubstitution(N,y,P))

// {

// }
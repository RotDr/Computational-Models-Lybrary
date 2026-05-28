include "Lambda.dfy"
include "BetaReduction.dfy"


ghost predicate parallelReduction(t1:LambdaTerm,t2:LambdaTerm)
    decreases lHeight(t1)
{
    t1==t2 ||
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
                    case _=> false
            ) 
            case Lambda(x,t1a) => (
                ( match t2 
                                        case Lambda(y,t2a)=> x==y && parallelReduction(t1a,t2a)
                                        case _ => false
            )
            )
            case _ => false
}

lemma parallelReductionIsReflexive (t:LambdaTerm)
    ensures parallelReduction(t,t)
{

}

lemma NoFreeVariablesToReplace (M:LambdaTerm,x:Id,P:LambdaTerm)
    requires !(x in free(M))
    ensures caSubstitution(M,x,P)==M 
{
    var ids:=reunion(vars(M),vars(P));
    reunionIncludesBothSets(vars(M),vars(P));
    NoFreeVariablesToReplace'(M,x,P,ids);
}
lemma NotInReunionSoNotInBoth(s1:seq<Id>,s2:seq<Id>,x:Id)
    requires allUnique(s1) && allUnique(s2)
    requires !(x in reunion(s1,s2))
    ensures !(x in s1) && !(x in s2)
{

}
lemma NoFreeVariablesToReplace' (M:LambdaTerm,x:Id,P:LambdaTerm,ids:seq<Id>)
    requires !(x in free(M))
    requires allUnique(ids)
    requires var s1:=vars(M);
         allUnique(s1) && includes(ids,s1)
    requires var s2:=vars(P);
         allUnique(s2)  && includes(ids,s2)
    ensures caSubstitution(M,x,P)==M 
{
    match M 
        case Var(y) =>{
            assert y in free(M);
            assert !(x in free(M));
            assert x!=y;

            assert caSubstitution'(M,x,P,ids)==M ;
        }
        case Application(M1,M2) => 
        {
            assert free(M)==reunion(free(M1),free(M2));
            NotInReunionSoNotInBoth(free(M1),free(M2),x);
            NoFreeVariablesToReplace'(M1,x,P,ids);
            assert caSubstitution'(M1,x,P,ids)==M1;
            NoFreeVariablesToReplace'(M2,x,P,ids);
            assert caSubstitution'(M2,x,P,ids)==M2;
            assert caSubstitution'(M,x,P,ids)==Application(caSubstitution'(M1,x,P,ids),caSubstitution'(M2,x,P,ids));
        }
        case Lambda(y,M') =>
        {
            if (y==x) 
            {
                assert caSubstitution'(M,x,P,ids)==M;
            }
            else 
            {
                if ()
            }
        }    
}

// lemma SubstitutionLemma (M:LambdaTerm,N:LambdaTerm,P:LambdaTerm,x:Id,y:Id)
//     requires x!=y
//     requires !(x in free(P))
//     ensures caSubstitution(caSubstitution(M,x,N),y,P)==caSubstitution(caSubstitution(M,y,P),x,caSubstitution(N,y,P))

// {
//     match M
//         case Application(M1,M2) =>
//         {

//         }
//         case Lambda(z,M')=>
//         {
            
//         }
//         case Var(z) => {
//             if (z==x) 
//             {
//                 var partial_result_left:=caSubstitution(M,x,N);
//                 assert M==Var(x);
//                 assert partial_result_left==N;
//                 var left_result:=caSubstitution(N,y,P);
//                 assert caSubstitution(caSubstitution(M,x,N),y,P)==left_result;

//                 assert x!=y;
//                 var partial_result_right:=caSubstitution(M,y,P);
//                 assert partial_result_right==M;
//                 var result_right:=caSubstitution(partial_result_right,x,caSubstitution(N,y,P));
//                 assert M==Var(x);
//                 assert result_right==caSubstitution(N,y,P);

//                 assert caSubstitution(caSubstitution(M,y,P),x,caSubstitution(N,y,P))==result_right;
                
//                 assert left_result=result_right;
                
//             }
//             if (z==y)
//             {
//                 var partial_result_left:=caSubstitution(M,x,N);
//                 assert M==Var(y);
//                 assert x!=y;
//                 assert partial_result_left==M;
//                 var left_result:=caSubstitution(M,y,P);
//                 assert caSubstitution(M,y,P)==P;
//                 assert caSubstitution(caSubstitution(M,x,N),y,P)==left_result;

//                 var partial_result_right:=caSubstitution(M,y,P);
//                 assert partial_result_right==P; 
//                 var right_result:=caSubstitution(P,caSubstitution(x,caSubstitution(N,y,P)));

//             }
//         } 
    
    

// }
include "LocallyNameless.dfy" 



function shiftPositive(t:RefLambdaTerm,l_count:nat) : RefLambdaTerm

{
    var result:=shiftPositive'(t,0,l_count);

    result
}

function shiftPositive'(t:RefLambdaTerm,og_count:nat,l_count:nat): RefLambdaTerm

{
    match t 
        case FreeVar(_)=> t
        case BoundVar(ref) => if ref>=og_count then BoundVar(ref+l_count) else BoundVar(ref)
        case App(t1,t2) => App(shiftPositive'(t1,og_count,l_count),shiftPositive'(t2,og_count,l_count))
        case RefLambda(t')=> RefLambda(shiftPositive'(t',og_count+1,l_count))

}

function shiftNegative(t:RefLambdaTerm,bytes:nat):RefLambdaTerm
    requires isRefReadyForNegativeShift(t,bytes)
{
     var result:=shiftNegative'(t,0,bytes);
    result
}


function shiftNegative'(t:RefLambdaTerm,l_count:nat,bytes:nat): RefLambdaTerm
    requires isRefReadyForNegativeShift'(t,l_count,bytes)
{
    match t 
        case FreeVar(_)=> t
        case BoundVar(ref) => if ref>=l_count then BoundVar(ref-bytes) else BoundVar(ref)
        case App(t1,t2) => App(shiftNegative'(t1,l_count,bytes),shiftNegative'(t2,l_count,bytes))
        case RefLambda(t')=> RefLambda(shiftNegative'(t',l_count+1,bytes))

}

lemma LemmaShiftPositiveValid(t: RefLambdaTerm, og_count: nat, l_count: nat, c: nat)
    requires locallyClosed'(t, c)
    requires og_count <= c
    ensures locallyClosed'(shiftPositive'(t, og_count, l_count), c + l_count)
{
     match t 
        case FreeVar(_)=> {}
        case BoundVar(ref) => if ref>=l_count {
        } else {
        }
        case App(t1,t2) => {
            
            LemmaShiftPositiveValid(t1,og_count,l_count,c);
            LemmaShiftPositiveValid(t2,og_count,l_count,c);
            assert locallyClosed'(App(shiftPositive'(t1,og_count,l_count),shiftPositive'(t2,og_count,l_count)),c+l_count);

        }
        case RefLambda(t')=> {
            
            LemmaShiftPositiveValid(t',og_count+1,l_count,c+1);
            assert locallyClosed'(RefLambda(shiftPositive'(t',og_count+1,l_count)),c+l_count);
            }
}


lemma LemmaShiftNegativeValid(t: RefLambdaTerm, l_count: nat, bytes: nat, c: nat)
    requires locallyClosed'(t, c)
    requires l_count + bytes <= c
    requires isRefReadyForNegativeShift'(t, l_count, bytes)
    ensures locallyClosed'(shiftNegative'(t, l_count, bytes), c - bytes)
{
    match t 
        case FreeVar(_)=> {}
        case BoundVar(ref) => if ref>=l_count {


        } else {


        }
        case App(t1,t2) => {
            
            LemmaShiftNegativeValid(t1,l_count,bytes,c);
            LemmaShiftNegativeValid(t2,l_count,bytes,c);
            assert locallyClosed'(App(shiftNegative'(t1,l_count,bytes),shiftNegative'(t2,l_count,bytes)),c-bytes);

        }
        case RefLambda(t')=> {
            
            LemmaShiftNegativeValid(t',l_count+1,bytes,c+1);
            assert locallyClosed'(RefLambda(shiftNegative'(t',l_count+1,bytes)),c-bytes);
            }
}

function refSubstitution (t:RefLambdaTerm,l_count:nat,t':RefLambdaTerm): RefLambdaTerm

{
    match t 
        case FreeVar(_) =>t 
        case BoundVar(ref) => if ref==l_count then t' 
                                    else if ref>l_count then BoundVar(ref-1)
                                        else t
        case App(t1,t2) => App(
            refSubstitution(t1,l_count,t'),
            refSubstitution(t2,l_count,t')
        )
        case RefLambda(t1)=>RefLambda(refSubstitution(t1,l_count+1,t'))

}


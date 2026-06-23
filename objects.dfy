datatype circuitCell = AND(pos1:nat,pos2:nat) | OR(pos1:nat,pos2:nat) | NOT(pos:nat) | VARIABLE(x:string) 
datatype Option<T> = Some(t:T) |None
type Id= nat
datatype LambdaTerm = Var(id:Id) | Lambda(x:Id,t:LambdaTerm) | Application( t1:LambdaTerm, t2:LambdaTerm)


function max(a:nat,b:nat) :nat 
    ensures var maxi:=max(a,b);
    maxi>=a && maxi>=b && (maxi==a || maxi==b)
{
    if a>b then a else b 
}

function minim (a:nat,b:nat) : nat
    ensures minim(a,b)<=a && minim(a,b)<=b
    ensures minim(a,b)==a || minim(a,b)==b
{
    if a>b then b 
    else a 
}

type circuit=seq<circuitCell>
type stringNat = s: string |
    |s| > 0 && (|s| > 1 ==> s[0] != '0') &&
    forall i | 0 <= i < |s| :: s[i] in "0123456789"
    witness "1"
const ReservedWords:=["AND","OR","NOT","TRUE","FALSE","CERTIFICATE"]
predicate isStringAValidNumber (s:string)
{
    |s| > 0 && (|s| > 1 ==> s[0] != '0') &&
    forall i | 0 <= i < |s| :: s[i] in "0123456789"
}
  function natToString(n: nat): string
    ensures isStringAValidNumber(natToString(n))
   {
    match n
    case 0 => "0" case 1 => "1" case 2 => "2" case 3 => "3" case 4 => "4"
    case 5 => "5" case 6 => "6" case 7 => "7" case 8 => "8" case 9 => "9"
    case _ => natToString(n / 10) + natToString(n % 10)
  }

  function stringToNat(s: string): nat
    decreases |s|
    requires isStringAValidNumber(s)
  {
    if |s| == 1 then
      match s[0]
      case '0' => 0 case '1' => 1 case '2' => 2 case '3' => 3 case '4' => 4
      case '5' => 5 case '6' => 6 case '7' => 7 case '8' => 8 case '9' => 9
    else
      stringToNat(s[..|s|-1])*10 + stringToNat(s[|s|-1..|s|])
  }
  lemma natToStringThenStringToNatIdem(n: nat)
    ensures stringToNat(natToString(n)) == n
  { 
  }
  lemma stringToNatThenNatToStringIdem(n: string)
    requires isStringAValidNumber(n)
    ensures natToString(stringToNat(n)) == n
  { 
  }
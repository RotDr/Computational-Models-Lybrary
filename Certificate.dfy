include "objects.dfy"
include "turing_machine.dfy"
type certificate=seq<string>
 predicate isCertificateCorrectForm (k:certificate)
{
    (|k|>0 && |k|%2==0) && (forall pos:nat:: pos<|k| ==> (if pos%2==1 then 
    (k[pos]!="TRUE" && k[pos]!="FALSE") 
    else (k[pos]=="TRUE" || k[pos]=="FALSE"))) 
}
 function findValue(k:certificate,v:string) : Option<bool>
    requires isCertificateCorrectForm(k)
    requires v!="TRUE" && v!="FALSE"
 {
    findValue'(k,v,1)
 }
 function findValue'(k:certificate,v:string,pos:nat): Option<bool>
    requires 0<pos<=|k|
    requires isCertificateCorrectForm(k)
    requires v!="TRUE" && v!="FALSE"
    decreases |k|-pos

 {
    if pos==|k| then 
        None
    else
        if k[pos]==v then
            if k[pos-1]=="TRUE" then 
                Some(true)
            else
                Some(false)
        else
            findValue'(k,v,pos+1)
 }
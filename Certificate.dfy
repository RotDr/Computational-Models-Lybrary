include "objects.dfy"
include "turing_machine.dfy"
type certificate=seq<string>
 predicate isCertificateCorrectForm (k:certificate)
{
    forall pos:nat:: pos<|k| ==> (k[pos]=="TRUE" || k[pos]=="FALSE")
}
 function findValue(k:certificate,pos:nat) : bool
    requires isCertificateCorrectForm(k)
    requires pos<|k|
 {
    if k[pos]=="TRUE" then true
    else false 
 }
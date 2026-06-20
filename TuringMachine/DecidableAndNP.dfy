include "DTM.dfy"
include "NDTM.dfy"

ghost predicate isTMADecider (delta:Transitions,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols,q0:State)
  requires isTapeSymbolsValid(inputS,addTapeS)
  requires isTransitionsValid(delta,inputS,addTapeS)
{
  forall input:seq<string> :: isInputValid(input,inputS) ==> haltsInTM(delta,q0,inputS,addTapeS,input)
}


ghost predicate isLanguageDecidable (lang:Language)
{
  exists delta:Transitions,q0:State,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols :: (isTapeSymbolsValid(inputS,addTapeS) 
  && isTransitionsValid(delta,inputS,addTapeS) 
  && isTMADecider(delta,inputS,addTapeS,q0) 
  && (isLanguageAcceptedInTM(delta,inputS,addTapeS,q0,lang) || isLanguageAcceptedInTMInPolynomialTime(delta,inputS,addTapeS,q0,lang))
  )
}





ghost predicate isLanguageNPTIME1 (lang:Language)
{
  exists delta:Transitions,q0:State,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols :: (isTapeSymbolsValid(inputS,addTapeS) 
  && isTransitionsValid(delta,inputS,addTapeS) 
  && isTMADecider(delta,inputS,addTapeS,q0) 
  && isLanguageAcceptedInTMInPolynomialTime(delta,inputS,addTapeS,q0,lang)
  && !isTransitionsDeterministic(delta,inputS,addTapeS))
}
ghost predicate isLanguageNPTIME2 (lang:Language)
{
  exists delta:Transitions,q0:State,inputS:InputSymbols,addTapeS:AdditionalTapeSymbols ::(isTapeSymbolsValid(inputS,addTapeS) 
  && isTransitionsValid(delta,inputS,addTapeS) 
  && isTMADecider(delta,inputS,addTapeS,q0) 
  && isTransitionsDeterministic(delta,inputS,addTapeS)
  && forall input:seq<string> :: (input in lang) <==> (exists c:seq<string> :: isInputValid(input+c,inputS) && isAcceptedInTMInPolynomialTime(delta,q0,inputS,addTapeS,input+c))
  )
}
lemma NPTIMEisDecidable (lang:Language)
  requires isLanguageNPTIME1(lang)
  ensures isLanguageDecidable(lang)
{

}

import DerridaRetaux.HumanInputs

/-!
# Published-input trust audit

The four full declarations are printed before their axiom dependencies.  Each axiom
report must contain exactly the declaration itself and no other nonstandard input.
-/

#print DerridaRetaux.EntranceString
#print DerridaRetaux.stringCumulative
#print DerridaRetaux.IsEntranceType
#print DerridaRetaux.HasSecondEntranceMoment
#print DerridaRetaux.NoRightBoundaryAmbiguity
#print DerridaRetaux.HasRightEnd
#print DerridaRetaux.EntranceString.translate
#print DerridaRetaux.IsEntranceNormalizedVolterraSolution
#print DerridaRetaux.HasSingularCharacteristic

#print DerridaRetaux.CDHLSExcessFact
#print DerridaRetaux.CDHLSProductFact
#print DerridaRetaux.KotaniCharacteristicFact
#print DerridaRetaux.ChenShiStableProductFact

#print DerridaRetaux.HumanInputs.cdhls_excess_upper
#print DerridaRetaux.HumanInputs.cdhls_product_upper
#print DerridaRetaux.HumanInputs.kotani_characteristic_eq_implies_translate
#print DerridaRetaux.HumanInputs.chenShi_stable_product

#print axioms DerridaRetaux.HumanInputs.cdhls_excess_upper
#print axioms DerridaRetaux.HumanInputs.cdhls_product_upper
#print axioms DerridaRetaux.HumanInputs.kotani_characteristic_eq_implies_translate
#print axioms DerridaRetaux.HumanInputs.chenShi_stable_product

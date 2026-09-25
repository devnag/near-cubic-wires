import Lean
import Proof.Assembly.CompilerLawsConstructionStep1
import Proof.Assembly.CompilerLawsConstructionStep3
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_d8d2a55d97139784d1c6190b.parent
  (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
  : (PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws) :=
  let body : (
    PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws
  ) := (
    @PCConstruction_1ff4ac18b523de3d69f177df.parent selector
  );
  (@PCConstruction_39d7a184cd3b2cb2ab6cb314.parent selector body)

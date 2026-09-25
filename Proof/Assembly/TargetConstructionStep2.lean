import Lean
import Proof.Assembly.EightSourcesConstructionStep2
import Proof.Assembly.TargetConstructionStep1
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_8c87b372610f47d82f1393a3.parent
  (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
  (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
  (tables : PCJ9eff70d512234a4c_Fixed.TableCertificate)
  (semantics : PCJ9eff70d512234a4c_Fixed.Certificate)
  (physical : PCJ9eff70d512234a4c_Fixed.PreparedRecipe selector compiler tables semantics)
  : (PCJ1fef9807c6954e94_Native.Target) :=
  @PCConstruction_ea9587c181acf6cdcb23e3e3.parent selector compiler tables semantics physical

import Lean
import Proof.Assembly.TableCertificateConstructionStep1
import Proof.Assembly.TableCertificateConstructionStep3
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_ff130191b384529c8fa196be.parent
  (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
  (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
  : (PCJ9eff70d512234a4c_Fixed.TableCertificate) :=
  let body : (
    PCJ9eff70d512234a4c_Fixed.TableCertificate
  ) := (
    @PCConstruction_58e22f35a4b12e3daaba0adf.parent selector compiler
  );
  (@PCConstruction_8a69d606ac5d04a3ca2def29.parent selector compiler body)

import Lean
import Proof.Assembly.CertificateConstructionStep1
import Proof.Assembly.CertificateConstructionStep3
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_d1e68290e6c53d4f6be92ee1.parent
  (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
  (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
  (tables : PCJ9eff70d512234a4c_Fixed.TableCertificate)
  : (PCJ9eff70d512234a4c_Fixed.Certificate) :=
  let body : (
    PCJ9eff70d512234a4c_Fixed.Certificate
  ) := (
    @PCConstruction_fe91857c003e329cf8ef217f.parent selector compiler tables
  );
  (@PCConstruction_69df5fcfa5b6d1de0c0bc4fc.parent selector compiler tables body)

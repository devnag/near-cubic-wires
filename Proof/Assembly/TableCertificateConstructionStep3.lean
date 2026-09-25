import Lean
import Proof.Assembly.RowSelectedTableSum
import Proof.Assembly.Sum
import Proof.Assembly.TableCertificateConstructionStep2
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_58e22f35a4b12e3daaba0adf.parent
  (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
  (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
  : (PCJ9eff70d512234a4c_Fixed.TableCertificate) :=
  let rows : (
    PCJ843c22a3684945e9_Plan.RowCertificate
  ) := (
    PCJ843c22a3684945e9_Row.certificate
  );
  let family : (
    PCJ843c22a3684945e9_Plan.RequestSum
  ) := (
    PCJ843c22a3684945e9_Sum.certificate
  );
  (@PCConstruction_b6226b9c5cf60c5835b031d9.parent selector compiler rows family)

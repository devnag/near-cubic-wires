import Lean
import Proof.Assembly.CertificateConstructionStep2
import Proof.Rows.Accuracy
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_fe91857c003e329cf8ef217f.parent
  (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
  (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
  (tables : PCJ9eff70d512234a4c_Fixed.TableCertificate)
  : (PCJ9eff70d512234a4c_Fixed.Certificate) :=
  let sym : (
    PCJa94fb905a93646cd.SymmetricAccuracy
  ) := (
    PCJa94fb905a93646cd.Chosen.symmetricAccuracy
  );
  let thr : (
    PCJa94fb905a93646cd.ThresholdAccuracy
  ) := (
    PCJa94fb905a93646cd.Chosen.thresholdAccuracy
  );
  (@PCConstruction_5a410f074c1323664dff73c3.parent selector compiler tables sym thr)

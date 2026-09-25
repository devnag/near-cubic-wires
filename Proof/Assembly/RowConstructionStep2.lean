import Proof.Assembly.RowConstructionStep1
import Proof.Rows.RowsInitAssemblyHole
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_9c86553efa4f63ee0095bde1.parent
  (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
  (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
  (tables : PCJ9eff70d512234a4c_Fixed.TableCertificate)
  (semantics : PCJ9eff70d512234a4c_Fixed.Certificate)
  (packetConstruction : PCJd4d1d9d7d1fa4313_Production.PacketConstruction fun {q m K} => @selector q m K)
  : (PCJd4d1d9d7d1fa4313_Production.RowConstruction fun {q m K} => @selector q m K) :=
  let rowsResidual : (
    PCJd4d1d9d7d1fa4313_Production.RowConstruction fun {q m K} => @selector q m K
  ) := (
    RowsConstruction.InitAssembly.rowConstruction_final selector
  );
  (@PCConstruction_dd957bc484b3427969e5c50f.parent selector compiler tables semantics packetConstruction rowsResidual)

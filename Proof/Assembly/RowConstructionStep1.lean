import Proof.Assembly.CachedRecipeConstructionStep2
import Proof.Packets.PacketsMetaCutoffMath
import Proof.Packets.PacketsMetaMul
import Proof.Assembly.RowsWarmHub
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_dd957bc484b3427969e5c50f.parent
  (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
  (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
  (tables : PCJ9eff70d512234a4c_Fixed.TableCertificate)
  (semantics : PCJ9eff70d512234a4c_Fixed.Certificate)
  (packetConstruction : PCJd4d1d9d7d1fa4313_Production.PacketConstruction fun {q m K} => @selector q m K)
  (rowsResidual : PCJd4d1d9d7d1fa4313_Production.RowConstruction fun {q m K} => @selector q m K)
  : (PCJd4d1d9d7d1fa4313_Production.RowConstruction fun {q m K} => @selector q m K) :=
  (fun (_ : True) => rowsResidual) RowsWarmHub.hub

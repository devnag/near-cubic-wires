import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Proof.Assembly.PlanOrdinaryCyclicMaskProduction
import Proof.Assembly.SourceAssemblyConstructionStep1
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_876baea7c58cdb1fc76799b3.parent
  (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
  (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
  (tables : PCJ9eff70d512234a4c_Fixed.TableCertificate)
  (semantics : PCJ9eff70d512234a4c_Fixed.Certificate)
  (packetConstruction : PCJd4d1d9d7d1fa4313_Production.PacketConstruction fun {q m K} => @selector q m K)
  (rowConstruction : PCJd4d1d9d7d1fa4313_Production.RowConstruction fun {q m K} => @selector q m K)
  (raw : PCJ93d4cfe17dc847a3.RawConstruction)
  : (PCJc4297ab269d8423a_Source.MaskConstruction) :=
  PCJ93d4cfe17dc847a3.parent raw

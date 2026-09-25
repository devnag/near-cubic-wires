import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Proof.Assembly.CachedRecipeConstructionStep1
import Proof.SourceAssembly.MaskSource
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_a78e4af9234f304250674cb5.parent
  (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
  (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
  (tables : PCJ9eff70d512234a4c_Fixed.TableCertificate)
  (semantics : PCJ9eff70d512234a4c_Fixed.Certificate)
  (packetConstruction : PCJd4d1d9d7d1fa4313_Production.PacketConstruction fun {q m K} => @selector q m K)
  (rowConstruction : PCJd4d1d9d7d1fa4313_Production.RowConstruction fun {q m K} => @selector q m K)
  (maskConstruction : PCJc4297ab269d8423a_Source.MaskConstruction)
  (remainingSource : PCJc4297ab269d8423a_Source.RemainingSource selector compiler tables semantics)
  : (PCJd4d1d9d7d1fa4313_Production.SourceAssembly (fun {q m K} => @selector q m K) compiler tables semantics) :=
  PCJc4297ab269d8423a_Source.parent selector compiler tables semantics maskConstruction remainingSource

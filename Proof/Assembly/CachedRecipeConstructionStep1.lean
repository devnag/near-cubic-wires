import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Proof.Assembly.PreparedRecipeConstructionStep3
import Proof.Assembly.SourceProduction
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_a2797f632f81c543e422de6f.parent
  (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
  (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
  (tables : PCJ9eff70d512234a4c_Fixed.TableCertificate)
  (semantics : PCJ9eff70d512234a4c_Fixed.Certificate)
  (packetConstruction : PCJd4d1d9d7d1fa4313_Production.PacketConstruction selector)
  (rowConstruction : PCJd4d1d9d7d1fa4313_Production.RowConstruction selector)
  (sourceAssembly : PCJd4d1d9d7d1fa4313_Production.SourceAssembly selector compiler tables semantics)
  : (PCJ38fbfed565f64139_Physical.CachedRecipe selector compiler tables semantics) :=
  PCJd4d1d9d7d1fa4313_Production.parent selector compiler tables semantics packetConstruction rowConstruction sourceAssembly

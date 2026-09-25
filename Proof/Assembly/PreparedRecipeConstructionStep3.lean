import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Proof.Assembly.Adapter
import Proof.Assembly.Assembly
import Proof.Assembly.Budget
import Proof.Assembly.ColdSource
import Proof.Assembly.FamilyFixedPhysicalRealization
import Proof.Assembly.TargetConstructionStep1
import Proof.Assembly.ValuesSym
import Proof.Assembly.ValuesThr
set_option linter.unusedVariables false
set_option linter.defProp false
noncomputable def PCConstruction_5a658f9d00ab3ec1ca4bfdbe.parent
  (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
  (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
  (tables : PCJ9eff70d512234a4c_Fixed.TableCertificate)
  (semantics : PCJ9eff70d512234a4c_Fixed.Certificate)
  (physical : PCJ38fbfed565f64139_Physical.CachedRecipe selector compiler tables semantics)
  : (PCJ9eff70d512234a4c_Fixed.PreparedRecipe selector compiler tables semantics) :=
  PCJ38fbfed565f64139_Physical.parent selector compiler tables semantics physical

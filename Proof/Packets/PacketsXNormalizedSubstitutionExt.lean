import Proof.Packets.PacketsXNormalizedFolds

/-! Substitution depends only on addresses that actually occur in its input.
This permits a physically accumulated delta-atom table without unused terminal
atoms when the frozen terminal window is zero. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedSubstitutionExt
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram

theorem on_support (a b : Nat→Ring.Poly Nat) (P : Ring.Poly Nat)
    (h : ∀m∈P,∀x∈m,a x=b x) :
    Normalized.structuralGF2Substitute a P=Normalized.structuralGF2Substitute b P := by
  rw [NormalizedFolds.substitute_foldr,NormalizedFolds.substitute_foldr]
  induction P with
  | nil=>rfl
  | cons m P ih=>
    simp only [List.foldr_cons]
    have hm : m.map a=m.map b := List.map_congr_left (fun x hx=>h m (by simp) x hx)
    rw [hm,ih (fun n hn=>h n (by simp [hn]))]

end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedSubstitutionExt

import Proof.Packets.PacketsXSubsetNormalizedOrder

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SingletonSubstitution
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram

variable (f : Nat→Nat)

theorem product_map (m : List Nat) :
    structuralGF2Product (m.map (fun code=>[[f code]]))=[m.map f] := by
  induction m with
  | nil=>rfl
  | cons code m ih=>
    simp only [List.map_cons,structuralGF2Product,List.foldr_cons]
    change structuralGF2Mul [[f code]] (structuralGF2Product (m.map (fun x=>[[f x]])))=_
    rw [ih]
    simp [structuralGF2Mul]

/-- Literal values of invalid positional indices are irrelevant: the actual
subset enumerator emits only coordinates below the resident code-bank size. -/
theorem substitute_congr_on (P : StructuralGF2Polynomial)
    (atom : Nat→StructuralGF2Polynomial)
    (ha : ∀m∈P,∀code∈m,atom code=[[f code]]) :
    structuralGF2Substitute atom P=P.map (List.map f) := by
  induction P with
  | nil=>rfl
  | cons m P ih=>
    have hm : m.map atom=m.map (fun code=>[[f code]]) :=
      List.map_congr_left (fun code hc=>ha m (by simp) code hc)
    change structuralGF2Add (structuralGF2Product (m.map atom)) (structuralGF2Substitute atom P)=_
    rw [hm,product_map f m,ih (fun n hn=>ha n (by simp [hn]))]
    rfl

end PCJ9eff70d512234a4c_Fixed.Materializer.SingletonSubstitution

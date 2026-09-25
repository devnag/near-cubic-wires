import Proof.Packets.PacketsXNormalizedRing
import Proof.Packets.PhysicalCoefficientAlgebra
import Mathlib.Data.List.OfFn

/-! Exact encoding bridge between fixed normalized monomials and ordinary
support-mask operations. No execution or size assertion is assumed here. -/
set_option autoImplicit false
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.PhysicalPacketMasks
open Ring

variable {B : Nat}

def mask (m : List (Fin B)) : List Bool :=
  List.ofFn (fun i : Fin B => decide (i ∈ m))

theorem mask_length (m : List (Fin B)) : (mask m).length = B := List.length_ofFn

theorem mask_canon (m : List (Fin B)) : mask (canon m) = mask m := by
  simp only [mask, canon_mem]

theorem mask_injective {m n : List (Fin B)}
    (hm : m.Pairwise (· < ·)) (hn : n.Pairwise (· < ·))
    (h : mask m = mask n) : m = n := by
  apply pairwise_toFinset_injective hm hn
  have hf := List.ofFn_inj.mp h
  ext i
  have hi := decide_eq_decide.mp (congrFun hf i)
  simpa only [List.mem_toFinset] using hi

abbrev Monomial (B : Nat) := {m : List (Fin B) // m.Pairwise (· < ·)}

def encode (m : Monomial B) : List Bool := mask m.val

theorem encode_injective : Function.Injective (encode (B:=B)) := by
  intro m n h
  exact Subtype.ext (mask_injective m.property n.property h)

end PCJ9eff70d512234a4c_Fixed.PhysicalPacketMasks

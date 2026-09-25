import Proof.Packets.NormalizerOrder
import Proof.Packets.PacketsXPhysicalPacketMasks

/-! The physical mask ordering equals the literal fixed Ring normalizer,
including duplicate-variable canonicalization and odd cancellation. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizerOrder
open PhysicalCoefficientAlgebra

variable {α β : Type} [DecidableEq α] [DecidableEq β]

theorem toggle_map (f : α→β) (hf : Function.Injective f) (x : α) (P : List α) :
    (toggle x P).map f=toggle (f x) (P.map f) := by
  unfold toggle
  have hm : f x∈P.map f ↔ x∈P := List.mem_map_of_injective hf
  by_cases hx : x∈P
  · rw [if_pos hx,if_pos (hm.mpr hx)]
    exact List.map_erase hf P
  · rw [if_neg hx,if_neg (fun h=>hx (hm.mp h))]
    rfl

theorem fold_toggle_map (f : α→β) (hf : Function.Injective f) (P A : List α) :
    (P.foldl (fun acc x=>toggle x acc) A).map f=
      (P.map f).foldl (fun acc x=>toggle x acc) (A.map f) := by
  induction P generalizing A with
  | nil => rfl
  | cons x P ih => simp only [List.foldl_cons,List.map_cons,ih,toggle_map f hf]

theorem ordered_map (f : α→β) (hf : Function.Injective f) (P : List α) :
    ordered (P.map f)=(ordered P).map f := by
  rw [ordered_eq_fold,ordered_eq_fold]
  exact (fold_toggle_map f hf P []).symm

variable {B : Nat}
def typedCanonical (m : List (Fin B)) : PhysicalPacketMasks.Monomial B :=
  ⟨Ring.canon m,Ring.canon_pairwise m⟩

theorem normalized_values (P : Ring.Poly (Fin B)) :
    (ordered (P.map typedCanonical)).map Subtype.val=Ring.norm P := by
  rw [ordered_eq_fold,fold_toggle_map Subtype.val Subtype.val_injective]
  simp only [List.map_nil,List.map_map,List.foldl_map]
  unfold Ring.norm
  apply congrArg (fun f=>List.foldl f [] P)
  funext acc m
  unfold typedCanonical Function.comp toggle Ring.toggle
  split
  · simp only [List.erase_eq_eraseP,beq_eq_decide]
  · rfl

/-- The normalization bank contains masks of the compiler's exact ordered
monomial list; this is stronger than coefficient equality or permutation. -/
theorem normalized_masks (P : Ring.Poly (Fin B)) :
    ordered (P.map PhysicalPacketMasks.mask)=(Ring.norm P).map PhysicalPacketMasks.mask := by
  have hinput : P.map PhysicalPacketMasks.mask=(P.map typedCanonical).map PhysicalPacketMasks.encode := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro m _
    exact (PhysicalPacketMasks.mask_canon m).symm
  rw [hinput,ordered_map PhysicalPacketMasks.encode PhysicalPacketMasks.encode_injective,←normalized_values]
  rw [List.map_map]
  apply List.map_congr_left
  intro m _
  rfl

end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizerOrder

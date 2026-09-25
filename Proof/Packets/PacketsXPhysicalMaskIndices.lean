import Proof.Packets.PacketsXPhysicalPacketMasks
import Proof.Packets.PhysicalMaskIndicesDefs

/-! Exact recovery of the ordered native indices from a canonical support mask. -/
set_option autoImplicit false
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.PhysicalMaskIndices

theorem selectedIndices_ge (offset : Nat) (support : List Bool) {k : Nat}
    (h : k ∈ selectedIndices offset support) : offset ≤ k := by
  induction support generalizing offset with
  | nil => simp [selectedIndices] at h
  | cons bit rest ih =>
    cases bit <;> simp only [selectedIndices, Bool.false_eq_true, if_false,
      List.nil_append, if_true, List.singleton_append, List.mem_cons] at h
    · exact (Nat.le_succ offset).trans (ih (offset+1) h)
    · rcases h with rfl | h
      · exact le_rfl
      · exact (Nat.le_succ offset).trans (ih (offset+1) h)

theorem selectedIndices_pairwise (offset : Nat) (support : List Bool) :
    (selectedIndices offset support).Pairwise (· < ·) := by
  induction support generalizing offset with
  | nil => simp [selectedIndices]
  | cons bit rest ih =>
    cases bit
    · simpa [selectedIndices] using ih (offset+1)
    · simp only [selectedIndices, if_true, List.singleton_append, List.pairwise_cons]
      exact ⟨fun k hk => selectedIndices_ge (offset+1) rest hk, ih (offset+1)⟩

theorem mem_selectedIndices_ofFn {B : Nat} (f : Fin B → Bool) (offset k : Nat) :
    k ∈ selectedIndices offset (List.ofFn f) ↔
      ∃ i : Fin B, f i = true ∧ k = offset+i.val := by
  induction B generalizing offset with
  | zero => simp [selectedIndices]
  | succ B ih =>
    simp only [List.ofFn_succ, selectedIndices, List.mem_append, ih,
      Fin.exists_fin_succ, Fin.val_zero, Nat.add_zero, Fin.val_succ]
    simp only [Nat.add_right_comm offset 1, Nat.add_assoc]
    cases f 0 <;> simp

/-- The machine's increasing traversal emits the exact original canonical list,
including the empty monomial and width zero. -/
theorem selectedIndices_mask {B : Nat} (m : List (Fin B))
    (hm : m.Pairwise (· < ·)) :
    selectedIndices 0 (PhysicalPacketMasks.mask m) = m.map Fin.val := by
  apply Ring.pairwise_toFinset_injective (selectedIndices_pairwise _ _)
    (List.pairwise_map.mpr hm)
  ext k
  simp only [List.mem_toFinset, PhysicalPacketMasks.mask,
    mem_selectedIndices_ofFn, decide_eq_true_eq, Nat.zero_add, List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩

end PCJ9eff70d512234a4c_Fixed.PhysicalMaskIndices

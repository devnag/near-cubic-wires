import Proof.Rows.PhysicalFocusBoundary

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.Dock
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch

/-! ## Padding algebra -/

theorem pad_append_zeros (R k : ℕ) (x : List Bool) (h : x.length + k ≤ R) :
    ZeroPadding.pad R (x ++ List.replicate k false) = ZeroPadding.pad R x := by
  simp only [ZeroPadding.pad, List.length_append, List.length_replicate, List.append_assoc,
    ← List.replicate_add]
  congr 2
  omega

theorem pad_nil_eq (R : ℕ) : ZeroPadding.pad R [] = List.replicate R false := by
  simp [ZeroPadding.pad]

theorem pad_zeros (R k : ℕ) (h : k ≤ R) :
    ZeroPadding.pad R (List.replicate k false) = ZeroPadding.pad R [] := by
  have := pad_append_zeros R k [] (by simpa using h)
  simpa using this

theorem pad_monotone (R S : ℕ) (x : List Bool) (h : R ≤ S) :
    ZeroPadding.pad S (ZeroPadding.pad R x) = ZeroPadding.pad S x := by
  by_cases hx : R ≤ x.length
  · have : ZeroPadding.pad R x = x := by
      simp [ZeroPadding.pad, show R - x.length = 0 by omega]
    rw [this]
  · simp only [ZeroPadding.pad]
    rw [List.append_assoc, ← List.replicate_add]
    congr 2
    simp only [List.length_append, List.length_replicate]
    omega

/-! ## The frame-form lift -/

theorem dock_slot {t u : ℕ} {α : Type} (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (ambient : Fin u → α) (localData : Fin t → α) (j : Fin t) :
    PCJ9eff70d512234a4c_Fixed.PhysicalFocusBoundary.dock slots ambient localData (slots j) = localData j := by
  simp only [PCJ9eff70d512234a4c_Fixed.PhysicalFocusBoundary.dock, RecoveryFocus.pick_slot slots hi j]

theorem dock_other {t u : ℕ} {α : Type} (slots : Fin t → Fin u)
    (ambient : Fin u → α) (localData : Fin t → α) (i : Fin u) (hn : ∀ j, slots j ≠ i) :
    PCJ9eff70d512234a4c_Fixed.PhysicalFocusBoundary.dock slots ambient localData i = ambient i := by
  cases hp : RecoveryFocus.pick slots i with
  | none => simp only [PCJ9eff70d512234a4c_Fixed.PhysicalFocusBoundary.dock, hp]
  | some j => exact absurd (RecoveryFocus.slot_of_pick slots hp) (hn j)

theorem lift {t u s n : ℕ} {p : Machine t s} {h0 h1 : Fin t → ℕ} {a0 a1 : Fin t → List Bool}
    (run : Step p n h0 a0 h1 a1) (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (cap : Fin t → ℕ) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hin : ∀ j, H (slots j) = h0 j ∧ A (slots j) = ZeroPadding.pad (cap j) (a0 j)) :
    ∃ (H' : Fin u → ℕ) (A' : Fin u → List Bool), Step (RecoveryFocus.machine slots p) n H A H' A' ∧
      (∀ j, H' (slots j) = h1 j ∧ A' (slots j) = ZeroPadding.pad (cap j) (a1 j)) ∧
      (∀ i, (∀ j, slots j ≠ i) → H' i = H i ∧ A' i = A i) := by
  refine ⟨PCJ9eff70d512234a4c_Fixed.PhysicalFocusBoundary.dock slots H h1,
    PCJ9eff70d512234a4c_Fixed.PhysicalFocusBoundary.dock slots A (fun j => ZeroPadding.pad (cap j) (a1 j)), ?_, ?_, ?_⟩
  · refine PCJ9eff70d512234a4c_Fixed.PhysicalFocusBoundary.focus (run.pad cap) slots hi H _ A _ ?_ ?_ ?_ ?_ ?_
    · intro j; exact (hin j).1.symm
    · intro j; exact (hin j).2.symm
    · intro j; exact (dock_slot slots hi H h1 j).symm
    · intro j; exact (dock_slot slots hi A (fun j => ZeroPadding.pad (cap j) (a1 j)) j).symm
    · intro i hn
      exact ⟨(dock_other slots H h1 i hn).symm, (dock_other slots A (fun j => ZeroPadding.pad (cap j) (a1 j)) i hn).symm⟩
  · intro j
    exact ⟨dock_slot slots hi H h1 j, dock_slot slots hi A (fun j => ZeroPadding.pad (cap j) (a1 j)) j⟩
  · intro i hn
    exact ⟨dock_other slots H h1 i hn, dock_other slots A (fun j => ZeroPadding.pad (cap j) (a1 j)) i hn⟩

end NearCubicWires.PacketsConstruction.Dock

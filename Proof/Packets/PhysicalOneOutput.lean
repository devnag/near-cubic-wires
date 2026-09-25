import Proof.Rows.PhysicalFocusBoundary

/-! A checked zero-head worker that changes one tape docks into any larger
resident bank and retains every unrelated tape and cursor. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalOneOutput
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch

theorem focus {k t s : Nat} (p : Machine k s) (E : Nat)
    (src : Fin k→List Bool) (d : Fin k) (word : List Bool)
    (run : Step p E (fun _=>0) src (fun _=>0) (Function.update src d word))
    (slots : Fin k→Fin t) (hinj : Function.Injective slots)
    (H : Fin t→Nat) (A : Fin t→List Bool)
    (hH : ∀j,H (slots j)=0) (hA : ∀j,A (slots j)=src j) :
    Step (RecoveryFocus.machine slots p) E H A H (Function.update A (slots d) word) := by
  apply PhysicalFocusBoundary.focus run slots hinj H H A (Function.update A (slots d) word)
  · intro j;exact (hH j).symm
  · intro j;exact (hA j).symm
  · intro j;exact (hH j).symm
  · intro j
    by_cases hj:j=d
    · subst j;simp
    · have hs : slots j≠slots d := fun he=>hj (hinj he)
      simp only [Function.update_of_ne hj,Function.update_of_ne hs]
      exact (hA j).symm
  · intro i away
    have hi:i≠slots d := by intro he;exact away d he.symm
    exact ⟨rfl,by simp [Function.update_of_ne hi]⟩

end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalOneOutput

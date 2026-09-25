import Proof.Rows.PhysicalFocusBoundary

/-! Focus a local actual run while retaining an arbitrary appended workspace. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalFocusAppend
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

theorem run {t u e s fuel : Nat} {p : Machine t s}
    {h0 h1 : Fin t→Nat} {a0 a1 : Fin t→List Bool} (h : Step p fuel h0 a0 h1 a1)
    (slots : Fin t→Fin u) (hinj : Function.Injective slots)
    (H0 H1 : Fin u→Nat) (A0 A1 : Fin u→List Bool)
    (EH : Fin e→Nat) (EA : Fin e→List Bool)
    (hs0 : ∀j,h0 j=H0 (slots j)) (as0 : ∀j,a0 j=A0 (slots j))
    (hs1 : ∀j,h1 j=H1 (slots j)) (as1 : ∀j,a1 j=A1 (slots j))
    (outside : ∀i,(∀j,slots j≠i)→H0 i=H1 i ∧ A0 i=A1 i) :
    Step (RecoveryFocus.machine (fun j=>(slots j).castAdd e) p) fuel
      (Fin.addCases H0 EH) (Fin.addCases A0 EA) (Fin.addCases H1 EH) (Fin.addCases A1 EA) := by
  apply PhysicalFocusBoundary.focus h (fun j=>(slots j).castAdd e)
    (by intro i j he;apply hinj;apply Fin.ext;exact congrArg (fun z : Fin (u+e)=>z.val) he)
    (Fin.addCases H0 EH) (Fin.addCases H1 EH) (Fin.addCases A0 EA) (Fin.addCases A1 EA)
  · intro j;rw [Fin.addCases_left];exact hs0 j
  · intro j;rw [Fin.addCases_left];exact as0 j
  · intro j;rw [Fin.addCases_left];exact hs1 j
  · intro j;rw [Fin.addCases_left];exact as1 j
  · intro i away
    revert away
    refine Fin.addCases (m:=u) (n:=e) (fun j=>?_) (fun j=>?_) i
    · intro away
      simp only [Fin.addCases_left]
      exact outside j (fun k he=>away k (congrArg (fun z : Fin u=>z.castAdd e) he))
    · intro _;simp only [Fin.addCases_right,and_self]

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalFocusAppend

import Proof.Packets.VectorBankTurnover

/-! The actual paid next-to-previous vector turnover in the complete arena.
The two Repeat drivers and all provider fields are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorController
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section


theorem banks_outside (B R ci pi li : Nat) (left right acc : List (List Bool))
    (previous next previous' next' : List Bool) (fields : Fin 222→List Bool)
    (i : Fin 264) (h0 : i≠256) (h1 : i≠257) :
    A B R ci pi li left right acc previous next fields i=
      A B R ci pi li left right acc previous' next' fields i := by
  revert h0 h1
  refine Fin.addCases (m:=256) (n:=8) (fun j=>?_) (fun j=>?_) i
  · intro _ _;unfold A;rw [Fin.addCases_left,Fin.addCases_left]
  · intro h0 h1
    have hj0 : j≠0 := by intro he;subst j;exact h0 rfl
    have hj1 : j≠1 := by intro he;subst j;exact h1 rfl
    rw [A_extra,A_extra]
    simp only [extraTapes,if_neg hj0,if_neg hj1]

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorController

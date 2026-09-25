import Proof.Packets.PacketsXWindowLiteralConsume

/-! The literal provider's endpoint preserves the complete reusable arithmetic
state, changing only the right operand to the exact normalized literal window. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram

theorem completed_core (C R : Nat) (left right result : List (List Bool)) (A : Fin 256→List Bool)
    (ha : ∀i : Fin 34,A (i.castAdd 222)=ReusableArithmetic.state C R left right i) :
    ∀i : Fin 34,completed R result A (i.castAdd 222)=ReusableArithmetic.state C R left result i := by
  intro i
  by_cases h26:i=26
  · subst i;rfl
  by_cases h27:i=27
  · subst i;rfl
  have n26 : i.castAdd 222≠(26 : Fin 256) := by
    intro he;apply h26;exact Fin.ext (congrArg (fun x : Fin 256=>x.val) he)
  have n27 : i.castAdd 222≠(27 : Fin 256) := by
    intro he;apply h27;exact Fin.ext (congrArg (fun x : Fin 256=>x.val) he)
  simp only [completed,Function.update_of_ne n26,Function.update_of_ne n27,ha]
  have h:=VectorAccumulator.tapes_right_outside C R left right result [] (i.castAdd 2)
    (by intro he;apply h26;exact Fin.ext (congrArg (fun x : Fin 36=>x.val) he))
    (by intro he;apply h27;exact Fin.ext (congrArg (fun x : Fin 36=>x.val) he))
  simpa only [VectorAccumulator.tapes_engine] using h

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider

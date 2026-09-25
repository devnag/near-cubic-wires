import Proof.Rows.MinimumMaskRun

/-! The output of the real native-sign pass is exactly the minimizing assignment
used by the residual-constant consumer, including q = 0 and zero weights. -/
set_option autoImplicit false
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_MinimumMaskMeaning
open NearCubicWires NearCubicWires.LocalBitMultitape
open PCJ45bee56da9f34d5a_MinimumMaskRun
noncomputable section

theorem output_eq {q : Nat} (g : NormalizedThresholdGate q) (live : Finset (Fin q)) (x : BitInput q) :
    output (List.ofFn g.weight) (List.ofFn (fun i=>decide (i∈live))) (List.ofFn x) q =
      List.ofFn (PCJ45bee56da9f34d5a_MinimumAssignment.input g live x) := by
  apply List.ext_getElem
  · simp [output]
  · intro j hleft hright
    have hj : j < q := by simpa using hright
    simp [output,PCJ45bee56da9f34d5a_MinimumMaskCell.bit,readTapeBit,List.getD,
      hj,PCJ45bee56da9f34d5a_MinimumAssignment.input]
end
end PCJ45bee56da9f34d5a_MinimumMaskMeaning

import Proof.CaseAnalysis.RowsCircuitBottomChecked

/-! One total bottom round loads the actual next field, runs the public
decoder, conditionally publishes its native request, folds validity, clears
the reusable gate scratch, and advances the original support cursor. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def loaded (threshold : Bool):=Composition.machine loader (checked threshold)
noncomputable def round (threshold : Bool):=Composition.machine (loaded threshold) finish

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom

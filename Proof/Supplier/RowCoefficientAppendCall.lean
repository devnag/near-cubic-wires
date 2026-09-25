import Proof.Supplier.RowCoefficientField

/-! Append the produced coefficient frame with the existing physical cursor
restore copier. Its reset workspace is supplied by the emitter's retained
log, so this handoff needs no separately manufactured capacity tape. -/
namespace NearCubicWires.RepairOrdinary.RowCoefficientAppendCall
open LocalBitMultitape RecoveryExecution RecoveryRootRound Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 3 → Fin 29 := ![26,28,27]
noncomputable def machine := RecoveryFocus.machine slots PCPSerializerReuse.copyMachine

end NearCubicWires.RepairOrdinary.RowCoefficientAppendCall

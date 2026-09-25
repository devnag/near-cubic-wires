import Proof.CaseAnalysis.RowsCircuitGateErase

/-! The original counted bottom traversal runs at the frozen full-circuit
ports. Its existing canonical stream is aliased, and its output prefix and
actual count template remain exact physical fields. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottomDock
open LocalBitMultitape RecoveryRootRound CloseoutRowsCircuit
open CloseoutRowsCircuitBottomLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def localHeads (position memberPos : ℕ) (out : List Bool) (D W : ℕ) : Fin 1060 → ℕ :=
  Fin.addCases (m:=1059) (n:=1) (CloseoutRowsCircuitBottom.heads position memberPos out D W) (fun _=>1)
def localTapes (C core n : ℕ) (out source members : List Bool) (D W : ℕ) (flag : Bool) :
    Fin 1060 → List Bool :=
  Fin.addCases (m:=1059) (n:=1) (CloseoutRowsCircuitBottom.data C core [] out source members D W flag)
    (fun _=>UnaryTemplate.tape n)
noncomputable def machine (threshold : Bool):=
  RecoveryFocus.machine bottomSlots (CloseoutRowsCircuitBottomLoop.machine threshold)

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottomDock

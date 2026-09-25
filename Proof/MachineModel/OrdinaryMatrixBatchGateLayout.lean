import Proof.MachineModel.OrdinaryMatrixBatchGateCopy

/-! Exact physical layout of the cold 166-tape batch entry and its native
49-tape all-gates consumer. Existing header and native fields are reused. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchGateLayout
open LocalBitMultitape RecoveryRootRound SignedSortKey MatrixScoreBatch
open MatrixScoreLeftLoop (C)
open MatrixScoreReusableRanks (D)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 49 → Fin 166 := ![132,95,133,134,135,136,49,137,138,139,140,141,142,143,144,77,107,92,61,65,145,146,147,32,148,106,149,39,99,150,151,152,153,154,155,156,157,158,159,160,161,162,163,103,130,164,1,165,89]
theorem slots_injective : Function.Injective slots := by decide
def heads (r : Request) : Fin 49 → ℕ := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,(header r).length,0,1]
def tapes (r : Request) : Fin 49 → List Bool := ![[],
  frame (binary r.d 0),
  [],
  [],
  [],
  [],
  List.replicate (r.S+1) true,
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  List.replicate (C r) true,
  List.replicate (C r+1) false,
  UnaryTemplate.tape r.d,
  frame (binary (r.S+1) (2^r.S)),
  frame (binary (r.S+1) 0),
  [],
  [],
  frame (binary r.M 0),
  frame (binary r.M r.U),
  [],
  List.replicate (C r) false,
  [],
  UnaryTemplate.tape r.U,
  frame (binary r.d 0),
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  frame (binary r.M 0),
  List.replicate (D r) true,
  [],
  word r,
  [],
  UnaryTemplate.tape r.Gates]

theorem native_heads (r : Request) :
    (MatrixBatchGateNativeLoop.cfg r 0 (word r) (header r).length [] (MatrixBatchGateNativeLoop.cold r)).heads=heads r := by
  rw [MatrixBatchGateNativeLoop.cfg_heads]
  funext i
  fin_cases i <;> rfl

theorem native_tapes (r : Request) :
    (MatrixBatchGateNativeLoop.cfg r 0 (word r) (header r).length [] (MatrixBatchGateNativeLoop.cold r)).tapes=tapes r := by
  rw [MatrixBatchGateNativeLoop.cfg_tapes]
  funext i
  fin_cases i <;> simp [MatrixBatchGateNativeLoop.cold,MatrixBatchGateClear.tapes,install,
    MatrixBatchGateClear.pick_scratch,MatrixBatchGateClear.scratchPick,MatrixBatchGateClear.stable,tapes,Fin.addCases]

end NearCubicWires.RepairOrdinary.MatrixBatchGateLayout

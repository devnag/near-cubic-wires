import Proof.CaseAnalysis.WitnessTermCircuitDock

/-! One literal term round. A failed coefficient never enters the circuit
worker, mass update or retained-record emission. A successful commit alone
enters the private circuit-bank reset. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermRound
open LocalBitMultitape RecoveryRootRound RecoveryExecution CanonicalWitnessCodec RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def begin := TapeEmbedding.machine 1705 TermBegin.machine
noncomputable def ending := TapeEmbedding.machine 1705 TermExit.machine
def flagSlots : Fin 2 → Fin 2532 := ![2527,719]
noncomputable def foldFlag := RecoveryFocus.machine flagSlots CloseoutRowsIntegerRound.flagMachine
private def stateCount {s : ℕ} (_ : Machine 2532 s) := s
noncomputable def sizes (s : ℕ) : Fin 5 → ℕ := ![stateCount begin,s,2,stateCount ending,4]
noncomputable def programs {s : ℕ} (circuit : Machine 1703 s) : (j : Fin 5) → Machine 2532 (sizes s j)
  | 0 => begin
  | 1 => RecoveryFocus.machine TermCircuitDock.slots circuit
  | 2 => foldFlag
  | 3 => ending
  | 4 => TermCircuitReset.machine
def next {s : ℕ} (j : Fin 5) (_ : Fin (sizes s j)) (bits : Fin 2532 → Bool) : Option (Fin 5) :=
  if j.val=0 then if bits 719 then some 1 else some 3
  else if j.val=1 then some 2 else if j.val=2 then some 3
  else if j.val=3 then if bits 724 then some 4 else none else none
noncomputable def machine {s : ℕ} (circuit : Machine 1703 s) :=
  RecoveryCalls.machine (sizes s) (programs circuit) 0 next

def heads (position : ℕ) (out : List Bool) (extra : Fin 1705 → ℕ) : Fin 2532 → ℕ :=
  Fin.addCases (m:=827) (n:=1705) (motive:=fun _=>ℕ) (TermCommit.heads position out) extra
def data (P : ℕ) (terms : Fin 725 → List Bool) (ambient : Fin 94 → List Bool)
    (out : List Bool) (extra : Fin 1705 → List Bool) : Fin 2532 → List Bool :=
  Fin.addCases (m:=827) (n:=1705) (motive:=fun _=>List Bool) (TermCommit.data P terms ambient out) extra

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermRound

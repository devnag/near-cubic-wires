import Proof.Rows.FinalNativeResidueInput
namespace NearCubicWires.RepairSource.CloseoutFinal.C10NativeResiduePrepare
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 6 → Fin 14 := ![4,9,10,11,12,13]
noncomputable def preparedMachine := Composition.machine
  (TapeEmbedding.machine 2 (MaskedReset.machine RecoveryRadixInput.machine (fun _=>true)))
  (RecoveryFocus.machine (![1,4,5] : Fin 3 → Fin 6) Streaming.machine)
noncomputable def first := TapeEmbedding.machine 5 DecompositionNativeMagnitude.first
noncomputable def last := RecoveryFocus.machine slots preparedMachine
noncomputable def machine := Composition.machine first last

def extras (D : ℕ) : Fin 5 → List Bool := ![[],[],List.replicate D false,[],[]]
def input (source : List Bool) (D : ℕ) : Fin 14 → List Bool :=
  Fin.addCases (motive := fun _=>List Bool) (DecompositionNativeMagnitude.input source 0).tapes (extras D)
def initialHeads (pos : ℕ) : Fin 14 → ℕ := fun i=>if i=0 then pos else 0
def heads (pos : ℕ) : Fin 14 → ℕ := fun i=>if i=0 then pos else if i=3 then 1 else 0

end NearCubicWires.RepairSource.CloseoutFinal.C10NativeResiduePrepare

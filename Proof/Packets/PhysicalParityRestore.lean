import Proof.Packets.PhysicalParityScan
import Proof.PCP.ProjectionNormalizationSuffixRestore

/-! A paid, reusable polynomial coefficient scanner. Both the candidate and
original polynomial source cursors return exactly to their original positions.
The returned coefficient is the GF(2) parity of all matching monomials. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace PhysicalParityRestore

noncomputable def machine := CursorRestore.machine PhysicalParityScan.machine 1
noncomputable def ending (candidate source : List Bool) (candidatePos sourcePos : ℕ)
    (eq found : Bool) (cap count log : ℕ) :=
  SelectiveReset.finished (s := Fintype.card (RepeatMachine.Control PhysicalParityReuse.size))
    (PhysicalParityScan.cfg 3 candidate source candidatePos sourcePos eq found cap count 1).heads
    (PhysicalParityScan.cfg 3 candidate source candidatePos sourcePos eq found cap count 1).tapes log

theorem source_forward : CursorRestore.NoLeft PhysicalParityScan.machine 1 := by
  have hp := CursorRestore.other_forward PhysicalParityProbe.raw (0 : Fin 4) 1 (by decide) (PhysicalParityProbe.raw_forward 1)
  exact CursorRestore.repeat_forward PhysicalParityProbe.machine (fun _ _ => true) (1 : Fin 5) hp

/-- The reserve only backs the erased cursor log. It adds no polynomial
bytes or precomputed coefficient to the entry bank. -/
noncomputable def input (candidate source : List Bool) (candidatePos sourcePos : Nat)
    (eq found : Bool) (cap count logCap : Nat) :=
  ZeroPadding.config (Rewind.Workspace.capacities 6 logCap)
    (Rewind.recording
      (PhysicalParityScan.cfg 0 candidate source candidatePos sourcePos eq found cap count 1) 0)

end PhysicalParityRestore
end NearCubicWires.RepairSource.ProjectionNormalization

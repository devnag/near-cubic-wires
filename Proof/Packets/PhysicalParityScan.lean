import Proof.Packets.PhysicalCoefficientAlgebra
import Proof.Packets.PhysicalParityReuse

namespace NearCubicWires.RepairSource.ProjectionNormalization.PhysicalParityScan
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Clause := Fin 3 → List Bool
def stream (rows : List Clause) := (rows.map ClauseEquality.stream).flatten
noncomputable def endEq (left : Clause) : List Clause → Bool → Bool
  | [],old => old
  | right::rows,_ => endEq left rows (decide (left=right))
noncomputable def seen (left : Clause) : List Clause → Bool → Bool
  | [], old => old
  | right::rows, old => seen left rows (xor old (decide (left=right)))
noncomputable def machine := RepeatMachine.machine PhysicalParityProbe.machine (fun _ _ => true)
noncomputable def cfg (phase : Fin 5) (candidate source : List Bool) (candidatePos sourcePos : ℕ)
    (eq found : Bool) (cap total driver : ℕ) :=
  RepeatMachine.cfg phase (PhysicalParityReuse.cfg PhysicalParityProbe.machine.start candidate source candidatePos sourcePos eq found cap) total driver

@[simp] theorem stream_nil : stream []=[] := rfl
@[simp] theorem stream_cons (row : Clause) (rows : List Clause) :
    stream (row::rows)=ClauseEquality.stream row++stream rows := rfl

theorem seen_cons (left right : Clause) (rows : List Clause) (old : Bool) :
    seen left rows (xor old (decide (left=right)))=seen left (right::rows) old := rfl

/-- The runtime parity bit is the sparse polynomial coefficient: each
matching monomial flips it once. This includes malformed/duplicate inputs. -/
theorem seen_coefficient (left : Clause) (rows : List Clause) (initial : Bool) :
    seen left rows initial = PhysicalCoefficientAlgebra.coefficient left rows initial := by
  classical
  induction rows generalizing initial with
  | nil => rfl
  | cons row rows ih =>
    exact ih (xor initial (decide (left = row)))

/-- One normalized monomial support as an existing variable-length framed
record; empty auxiliary fields make the encoding independent of its width. -/
def supportRecord (support : List Bool) : Clause := ![support, [], []]

theorem supportRecord_injective : Function.Injective supportRecord := by
  intro left right h
  exact congrArg (fun row : Clause => row 0) h

end NearCubicWires.RepairSource.ProjectionNormalization.PhysicalParityScan

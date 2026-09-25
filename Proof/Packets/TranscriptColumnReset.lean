import Proof.Packets.TranscriptColumnReuse
import Proof.Packets.PhysicalZeroBankOverwrite
import Proof.Packets.VectorCounter

/-! The physical transition between candidate columns: clear the consumed
column without shrinking its allocation, then advance the actual padded
candidate driver. Width, row count, visit count and packet operands survive. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.TranscriptColumn
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def clearSlots : Fin 4 → Fin 9 := ![0,6,5,7]
def clearColumn := RecoveryFocus.machine clearSlots PhysicalZeroBank.machine

def clearTapes (R T S : Nat) (bank : List Bool) : Fin 4 → List Bool :=
  ![ZeroPadding.pad S (UnaryTemplate.tape R),bank,List.replicate S false,CompareMachine.word T]

private theorem clear_heads : ∀j,PhysicalZeroBank.heads 0 j=heads 0 0 (clearSlots j) := by
  intro j;fin_cases j <;> rfl
private theorem clear_tapes (R N T column S : Nat) (source payload count bank : List Bool) :
    ∀j,clearTapes R T S bank j=residentTapes R N T column S source payload count bank (clearSlots j) := by
  intro j;fin_cases j <;> rfl
private theorem clear_outside (R N T column S : Nat) (source payload count bank result : List Bool) :
    ∀i,(∀j,clearSlots j≠i)→
      residentTapes R N T column S source payload count bank i=
        residentTapes R N T column S source payload count result i := by
  intro i away
  have hi : i≠6 := by intro he;exact away 1 he.symm
  fin_cases i <;> simp_all [residentTapes]

theorem clear_column (R N T column S : Nat) (source payload count bank : List Bool)
    (hlen : bank.length=T*(2*R)) :
    Step clearColumn (PhysicalZeroBank.budget R T) (heads 0 0)
      (residentTapes R N T column S source payload count bank) (heads 0 0)
      (residentTapes R N T column S source payload count (List.replicate (T*(2*R)) false)) := by
  have small := (PhysicalZeroBank.overwrite_run R T bank hlen).pad (![S,0,S,0] : Fin 4 → Nat)
  have padded (word : List Bool) :
      (fun i=>ZeroPadding.pad ((![S,0,S,0] : Fin 4 → Nat) i) (PhysicalZeroBank.tapes R T word i))=
        clearTapes R T S word := by
    funext i;fin_cases i <;> simp [PhysicalZeroBank.tapes,clearTapes,ZeroPadding.pad_zero,ZeroPadding.pad]
  rw [padded,padded] at small
  exact PhysicalFocusBoundary.focus small clearSlots (by decide) (heads 0 0) (heads 0 0) _ _
    clear_heads (clear_tapes R N T column S source payload count bank)
    clear_heads (clear_tapes R N T column S source payload count _)
    (fun i away=>⟨rfl,clear_outside R N T column S source payload count bank _ i away⟩)

def candidateSlot : Fin 1 → Fin 9 := fun _=>8
def incrementCandidate := RecoveryFocus.machine candidateSlot VectorCounter.increment

theorem increment_candidate (R N T column S : Nat) (source payload count bank : List Bool) :
    Step incrementCandidate (2*column+2) (heads 0 0)
      (residentTapes R N T column S source payload count bank) (heads 0 0)
      (residentTapes R N T (column+1) S source payload count bank) := by
  apply PhysicalFocusBoundary.focus (VectorCounter.increment_padded column S) candidateSlot
    (by intro i j _;exact Subsingleton.elim i j) (heads 0 0) (heads 0 0) _ _
  · intro i;rfl
  · intro i;rfl
  · intro i;rfl
  · intro i;rfl
  · intro i away
    have hi : i≠8 := by intro he;exact away 0 he.symm
    constructor
    · rfl
    · fin_cases i <;> simp_all [residentTapes]

def resetNext := Composition.machine clearColumn incrementCandidate
def resetBudget (R T column : Nat) := PhysicalZeroBank.budget R T+2*column+3

theorem reset_next (R N T column S : Nat) (source payload count bank : List Bool)
    (hlen : bank.length=T*(2*R)) :
    Step resetNext (resetBudget R T column) (heads 0 0)
      (residentTapes R N T column S source payload count bank) (heads 0 0)
      (residentTapes R N T (column+1) S source payload count (List.replicate (T*(2*R)) false)) := by
  have first := clear_column R N T column S source payload count bank hlen
  have last := increment_candidate R N T column S source payload count (List.replicate (T*(2*R)) false)
  have whole := first.seq last
  simpa only [resetNext,resetBudget,show PhysicalZeroBank.budget R T+1+(2*column+2)=
    PhysicalZeroBank.budget R T+2*column+3 by omega] using whole

end
end PCJ9eff70d512234a4c_Fixed.Materializer.TranscriptColumn

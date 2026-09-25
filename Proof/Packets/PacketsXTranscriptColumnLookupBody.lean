import Proof.Packets.PacketsXTranscriptColumnLookupStep
import Proof.Packets.PacketsXSelectedFactorStep

/-! The lookup body pays both descending cursors before using the actual
candidate's bit and packet. The selected left operand is added even when zero. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.TranscriptColumnLookupBody
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds SelectedPairFetch

noncomputable def machine := Composition.machine SelectedFactorStep.move
  (Composition.machine SelectedPairFetch.retreat TranscriptColumnLookupStep.machine)
def budget (C w : Nat) := 128*(commonReserve C w+1)^2

theorem run (C w i : Nat) (ps : List Poly) (left acc : Poly) (bits : List Bool) (flag : Bool)
    (hb : readTapeBit bits i=flag) (hi : i<ps.length) (hR : i+2≤commonReserve C w)
    (hl : left.length≤2^w) (hps : ∀P∈ps,P.length≤2^w)
    (hp : Fits C (ps.getD i [])) (hq : Fits C acc) (np : Ring.Normal (ps.getD i []))
    (nq : Ring.Normal acc) (hacc : acc.length≤2^w) (hw : 1≤w) :
    let chosen := if flag then ps.getD i [] else []
    Step machine (budget C w) (H (i+1)) (A C (commonReserve C w) (i+1) left acc ps bits)
      (H i) (A C (commonReserve C w) i chosen (Ring.add chosen acc) ps bits) := by
  dsimp only
  let j : Fin ps.length := ⟨i,hi⟩
  rw [List.getD_eq_getElem _ _ hi] at hp np ⊢
  have first:=SelectedFactorStep.move_run C (commonReserve C w) (i+1) i left acc ps bits
  have second:=SelectedPairFetch.retreat_run C (commonReserve C w) i i left acc ps bits hR
  have third:=TranscriptColumnLookupStep.run C w i ps j left acc bits flag hb hl hps hp hq np nq hacc hw
  have all:=first.seq (second.seq third)
  apply all.enlarge
  have hb:=TranscriptColumnLookupStep.budget_bound C w i (by omega)
  unfold budget
  nlinarith

end PCJ9eff70d512234a4c_Fixed.Materializer.TranscriptColumnLookupBody

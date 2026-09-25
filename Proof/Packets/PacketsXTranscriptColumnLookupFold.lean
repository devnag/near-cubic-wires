import Proof.Packets.PacketsXTranscriptColumnLookupBody
import Proof.Packets.PacketsXTranscriptColumnLookupMeaning

/-! A real descending counted scan of the original coordinate bank and actual
lookup bits, yielding the exact original one-hot polynomial, including every
zero addition in its prescribed order. No filtered packet bank is an input. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.TranscriptColumnLookupFold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds TranscriptColumnLookupMeaning
noncomputable def machine := RepeatMachine.machine TranscriptColumnLookupBody.machine (fun _ _=>true)
def budget (C w N : Nat) := N*(TranscriptColumnLookupBody.budget C w+3)+3
def H (pos : Nat) : Fin 39→Nat := Fin.addCases (m:=38) (n:=1) (motive:=fun _=>Nat)
  (SelectedPairFetch.H pos) (fun _=>1)
def A (C R index N : Nat) (left acc : Poly) (ps : List Poly) (bits : List Bool) : Fin 39→List Bool :=
  Fin.addCases (m:=38) (n:=1) (motive:=fun _=>List Bool)
    (SelectedPairFetch.A C R index left acc ps bits) (fun _=>CompareMachine.word N)

end PCJ9eff70d512234a4c_Fixed.Materializer.TranscriptColumnLookupFold

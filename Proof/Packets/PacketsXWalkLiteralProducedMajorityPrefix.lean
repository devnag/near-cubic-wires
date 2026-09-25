import Proof.Packets.PacketsXWalkLiteralProducedMajorityResident
import Proof.Packets.PacketsXWalkLiteralProducedMajorityFinish
import Proof.Packets.PacketsXWalkTranscriptColumnAllLayout

/-! One actual prefix from the rewound walk transcript to initialized
majority state around its physically extracted first time column. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralProducedMajority
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer Completion
open VectorBottomUp CloseoutRowsModeCache
noncomputable section
variable {population active depth n : Nat}
attribute [local irreducible] front firstColumn lowerTime finishReady

def columnWords (C w : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1)) :=
  TranscriptColumn.residentTapes (R C w) (population+1) (n+1) 0 (S C w)
    (PacketTranscript.prefixBank (R C w) (WalkLiteralLoop.rows C mask wins sample) (n+1))
    (PacketVector.payload (R C w) (WalkTranscriptColumn.allLast C mask wins sample 0))
    (PacketVector.count (R C w) (WalkTranscriptColumn.allLast C mask wins sample 0))
    (OrderedPacketStep.bank C (R C w) (WalkTranscriptColumn.allPolys mask wins sample 0))
def firstBank (C w root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (codeTail : List Bool) (masters : Fin 95→List Bool) (work : Fin 299→List Bool) :=
  install columnSlots (scalarBank C (R C w) n (zeroBank (S C w) (walkBank C w root mask wins sample codeTail masters work)))
    (columnWords C w mask wins sample)
def prefixBank (C w root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (codeTail : List Bool) (masters : Fin 95→List Bool) (work : Fin 299→List Bool) :=
  finishedBank C (R C w) n (WalkTranscriptColumn.allPolys mask wins sample 0)
    (firstBank C w root mask wins sample codeTail masters work)
def prefixHeads (n : Nat) := readyHeads (loweredHeads (scalarHeads (walkHeads n)))
def prefixMachine := Composition.machine front (Composition.machine firstColumn (Composition.machine lowerTime finishReady))
def prefixBudget (C w population n : Nat) :=
  frontBudget (S C w) n+1+(2+TranscriptColumn.budget (R C w) (population+1) (n+1) 0+1+
    (1+1+(finishBudget (R C w)+2)))

theorem first_extract (C w d root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (h : WalkLiteralLoop.Bounds C w d population active depth root (S C w) (R C w) wins)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (codeTail : List Bool) (masters : Fin 95→List Bool) (work : Fin 299→List Bool)
    (ready : TranscriptRewindReady (R C w) (S C w) (population+1) work) :
    Step firstColumn (2+TranscriptColumn.budget (R C w) (population+1) (n+1) 0)
      (scalarHeads (walkHeads n))
      (scalarBank C (R C w) n (zeroBank (S C w) (walkBank C w root mask wins sample codeTail masters work)))
      (raisedHeads (scalarHeads (walkHeads n))) (firstBank C w root mask wins sample codeTail masters work) := by
  have hR : 1≤R C w := by
    change 1≤CycleBounds.commonReserve C w
    have hd:=h.decode
    omega
  have hRS : R C w≤S C w := by
    change CycleBounds.commonReserve C w≤S C w
    have hs:=h.reserve
    omega
  have hempty : PacketVector.Fits (R C w) [] := by simpa [PacketVector.Fits,CompareMachine.word] using hR
  have hc : (WalkTranscriptColumn.allColumn population 0).val=0 :=
    WalkTranscriptColumn.allColumn_val population 0 (Nat.zero_le _)
  have pin:=scalar_column_pin C w root mask wins sample codeTail masters work hR hRS ready
  have actual:=first_column_run (R C w) (population+1) (n+1) (S C w)
    (WalkLiteralLoop.rows C mask wins sample) (WalkLiteralLoop.rows_length C mask wins sample)
    (WalkTranscriptColumn.allColumn population 0) (WalkLiteralLoop.rows_fits C w d root (S C w) (R C w) mask wins h sample)
    hempty _ _ (scalar_column_heads n) (by simpa only [hc] using pin)
  rw [WalkTranscriptColumn.column_packets] at actual
  simpa only [hc,TranscriptColumn.previous_succ,WalkTranscriptColumn.row_packet,firstBank,columnWords,
    WalkTranscriptColumn.allLast,WalkTranscriptColumn.allPolys,OrderedPacketStep.bank] using actual

theorem first_cold (C w root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (codeTail : List Bool) (masters : Fin 95→List Bool) (work : Fin 299→List Bool) :
    ∀j,firstBank C w root mask wins sample codeTail masters work (coldSlots j)=
      MajorityComplete.Cold.afterScalar C (R C w) n
        (OrderedPacketStep.bank C (R C w) (WalkTranscriptColumn.allPolys mask wins sample 0)) j := by
  apply column_cold_view
  · intro j
    exact install_slot coldSlots cold_injective _ _ j
  · rfl
  · rfl

theorem prefix_run (C w d root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (h : WalkLiteralLoop.Bounds C w d population active depth root (S C w) (R C w) wins)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (hVisits : n+1≤2^w) (hCodes : 2^(n+1)≤2^w)
    (codeTail : List Bool) (masters : Fin 95→List Bool) (work : Fin 299→List Bool)
    (ready : TranscriptRewindReady (R C w) (S C w) (population+1) work) :
    Step prefixMachine (prefixBudget C w population n) (walkHeads n) (walkBank C w root mask wins sample codeTail masters work)
      (prefixHeads n) (prefixBank C w root mask wins sample codeTail masters work) := by
  have first:=walk_front C w root mask wins sample codeTail masters work
  have second:=first_extract C w d root mask wins h sample codeTail masters work ready
  have third:=lower_time_run (scalarHeads (walkHeads n)) (firstBank C w root mask wins sample codeTail masters work)
  have heads : ∀j,loweredHeads (scalarHeads (walkHeads n)) (coldSlots j)=0 := by
    apply lowered_cold
    intro j
    exact dockH_slot coldSlots cold_injective _ _ j
  have last:=finish_ready_run C w n (WalkTranscriptColumn.allPolys mask wins sample 0)
    (WalkTranscriptColumn.allPolys_length mask wins sample 0) hVisits hCodes
    (by have hw:=h.width;omega) _ _ heads (first_cold C w root mask wins sample codeTail masters work)
  exact first.seq (second.seq (third.seq last))

end
end Theorem25Completion.WalkLiteralProducedMajority

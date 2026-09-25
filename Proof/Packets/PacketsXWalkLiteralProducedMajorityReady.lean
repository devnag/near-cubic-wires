import Proof.Packets.PacketsXWalkLiteralProducedMajorityPrefix
import Proof.Packets.PacketsXWalkTranscriptColumnReady

/-! The physically prepared742-tape state projects to the checked controller
invariant. The outer population driver and fresh result bank are actual tapes. -/
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

theorem lower_column_heads (H : Fin 742→Nat) (hh : ∀j,H (columnSlots j)=columnStartHeads j) :
    ∀j,loweredHeads H (columnSlots j)=Function.update (TranscriptColumn.heads 0 0) 7 0 j := by
  intro j
  by_cases hj:j=7
  · subst j;exact Function.update_self _ _ _
  · have hs : columnSlots j≠709 := by intro he;exact hj (column_injective he)
    rw [loweredHeads,Function.update_of_ne hs,raised_column H hh,Function.update_of_ne hj]

theorem prefix_unchanged (C w root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (codeTail : List Bool) (masters : Fin 95→List Bool) (work : Fin 299→List Bool) (k : Fin 742)
    (hc : ∀j,coldSlots j≠k) (hz : ∀j,zeroSlots j≠k) (he : ∀j,columnSlots j≠k)
    (hr : ∀j,raiseSlots j≠k) (ht : k≠709) :
    prefixBank C w root mask wins sample codeTail masters work k=walkBank C w root mask wins sample codeTail masters work k ∧
      prefixHeads n k=walkHeads n k := by
  constructor
  · rw [prefixBank,finishedBank,install_other _ _ _ _ hc,firstBank,install_other _ _ _ _ he,
      scalarBank,install_other _ _ _ _ hc,zeroBank,install_other _ _ _ _ hz]
  · rw [prefixHeads,readyHeads,Function.update_of_ne ht,finishedHeads,dockH_other _ _ _ _ hc,
      loweredHeads,Function.update_of_ne ht,raisedHeads,dockH_other _ _ _ _ hr,scalarHeads,dockH_other _ _ _ _ hc]

theorem prefix_result (C w root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (codeTail : List Bool) (masters : Fin 95→List Bool) (work : Fin 299→List Bool) :
    prefixBank C w root mask wins sample codeTail masters work 704=[] ∧ prefixHeads n 704=0 := by
  have h:=prefix_unchanged C w root mask wins sample codeTail masters work 704
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have hw:=walk_high C w root mask wins sample codeTail masters work 704 (by decide)
  exact ⟨h.1.trans hw.1,h.2.trans hw.2⟩

theorem prefix_driver (C w root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (codeTail : List Bool) (masters : Fin 95→List Bool) (work : Fin 299→List Bool) :
    prefixBank C w root mask wins sample codeTail masters work 93=ZeroPadding.pad (R C w) (CompareMachine.word population) ∧
      prefixHeads n 93=0 := by
  have h:=prefix_unchanged C w root mask wins sample codeTail masters work 93
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨h.1.trans (walk_cold_word C w root mask wins sample codeTail masters work 29),
    h.2.trans (walk_cold_head n 29)⟩

theorem prefix_ready (C w root : Nat) (mask : Finset (Fin population)) (wins : Fin depth→Nat)
    (sample : MargulisWalkSample (2^toeplitzWalkSideBits (canonicalGradedRank population active)) (n+1))
    (codeTail : List Bool) (masters : Fin 95→List Bool) (work : Fin 299→List Bool) :
    WalkTranscriptColumnArena.Ready (MajorityComplete.Cold.masters C (R C w) (n+1) ((R C w)^2))
      C (R C w) ((R C w)^2) (population+1) (n+1) (S C w) 0
      (PacketTranscript.prefixBank (R C w) (WalkLiteralLoop.rows C mask wins sample) (n+1))
      (WalkTranscriptColumn.allLast C mask wins sample 0)
      (OrderedPacketStep.bank C (R C w) (WalkTranscriptColumn.allPolys mask wins sample 0)) []
      (WalkTranscriptColumn.allPolys mask wins sample 0)
      (fun j=>prefixBank C w root mask wins sample codeTail masters work (workerSlots j)) ∧
    WalkTranscriptColumnArena.ReadyHeads (fun j=>prefixHeads n (workerSlots j)) 0 := by
  have col : ∀j,prefixBank C w root mask wins sample codeTail masters work (columnSlots j)=columnWords C w mask wins sample j := by
    apply ready_column_words
    · intro j;exact install_slot columnSlots column_injective _ _ j
    · rfl
    · rfl
  have heads:=ready_column_heads (loweredHeads (scalarHeads (walkHeads n)))
    (lower_column_heads (scalarHeads (walkHeads n)) (scalar_column_heads n))
  have result:=prefix_result C w root mask wins sample codeTail masters work
  constructor
  · constructor
    · intro j;rw [←column_worker];exact col j
    · intro j _;rw [←majority_worker];exact ready_majority_words _ _ _ _ _ j
    · exact result.1
  · constructor
    · intro j;rw [←column_worker];exact heads j
    · intro j;rw [←majority_worker];exact ready_majority_heads _ j
    · exact result.2

theorem controller_cover (i : Fin 472) (hi:i≠29) :
    ∃j : Fin 471,WalkTranscriptColumnController.slots (j.castAdd 1)=i := by
  have hb : (WalkTranscriptColumnController.slots i).val<471 := by
    by_cases ht:i=471
    · subst i;decide
    · simp only [WalkTranscriptColumnController.slots,if_neg hi,if_neg ht]
      have hv:=i.isLt
      have hne : i.val≠471 := by intro he;exact ht (Fin.ext he)
      omega
  let j : Fin 471:=⟨(WalkTranscriptColumnController.slots i).val,hb⟩
  have he : j.castAdd 1=WalkTranscriptColumnController.slots i := Fin.ext rfl
  exact ⟨j,by rw [he,WalkTranscriptColumnController.slots_twice]⟩

theorem controller_word_view (R population : Nat) (A : Fin 742→List Bool)
    (driver : A (controllerSlots 29)=ZeroPadding.pad R (CompareMachine.word population)) :
    ∀j,A (controllerSlots j)=WalkTranscriptColumnController.tapes R population (fun i=>A (workerSlots i)) j := by
  intro j
  by_cases hj:j=29
  · subst j;exact driver
  · obtain ⟨i,rfl⟩:=controller_cover j hj
    simp only [WalkTranscriptColumnController.tapes,WalkTranscriptColumnController.slots_twice,Fin.addCases_left]
    rfl

theorem controller_head_view (H : Fin 742→Nat) (driver : H (controllerSlots 29)=0) :
    ∀j,H (controllerSlots j)=Function.update
      (WalkTranscriptColumnController.heads (fun i=>H (workerSlots i))) 29 0 j := by
  intro j
  by_cases hj:j=29
  · subst j;simpa only [Function.update_self] using driver
  · rw [Function.update_of_ne hj]
    obtain ⟨i,rfl⟩:=controller_cover j hj
    simp only [WalkTranscriptColumnController.heads,WalkTranscriptColumnController.slots_twice,Fin.addCases_left]
    rfl

end
end Theorem25Completion.WalkLiteralProducedMajority

import Proof.Packets.PacketsXMajorityCompleteColdLayout

/-! Paid simultaneous copies of the ten actual scalar results into the
retained majority palette. The quadratic driver is reused without copying it. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Cold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open Theorem25Completion.CycleBounds Completion.SourceDock
noncomputable section

theorem scalar_N (n : Nat) : scalarOutput n 5=CompareMachine.word (n+1) :=
  (Classical.choose_spec (Completion.MajorityScalarProducer.run n)).2.1
theorem scalar_half (n : Nat) : scalarOutput n 7=CompareMachine.word ((n+1+1)/2) :=
  (Classical.choose_spec (Completion.MajorityScalarProducer.run n)).2.2.1
theorem scalar_one (n : Nat) : scalarOutput n 9=CompareMachine.word 1 :=
  (Classical.choose_spec (Completion.MajorityScalarProducer.run n)).2.2.2.1
theorem scalar_bits (n : Nat) : scalarOutput n 11=frame (SignedSortKey.binary (n+1) 0) :=
  (Classical.choose_spec (Completion.MajorityScalarProducer.run n)).2.2.2.2.1
theorem scalar_counter (n : Nat) : scalarOutput n 28=CompareMachine.word (2^(n+1)-1) :=
  (Classical.choose_spec (Completion.MajorityScalarProducer.run n)).2.2.2.2.2.1
theorem scalar_power (n : Nat) : scalarOutput n 26=UnaryTemplate.tape (2^(n+1)) :=
  (Classical.choose_spec (Completion.MajorityScalarProducer.run n)).2.2.2.2.2.2

theorem copy_source (C R n : Nat) (source : List Bool) (i : Fin 10) :
    afterSquare C R n source (copySlots ((i.castAdd 11).castAdd 1))=palette C R (n+1) i := by
  fin_cases i
  · rw [afterSquare,install_other widthSlots _ _ _ (by decide),
      afterScalar,install_other scalarSlots _ _ _ (by decide)]
    rfl
  · rw [afterSquare,install_other widthSlots _ _ _ (by decide),
      afterScalar,install_other scalarSlots _ _ _ (by decide)]
    rfl
  · change install widthSlots _ _ (widthSlots 0)=_
    rw [install_slot widthSlots width_injective]
    exact Width.source R
  · rw [afterSquare,install_other widthSlots _ _ _ (by decide),
      afterScalar,install_other scalarSlots _ _ _ (by decide)]
    rfl
  · rw [afterSquare,install_other widthSlots _ _ _ (by decide)]
    change install scalarSlots _ _ (scalarSlots 9)=_
    rw [install_slot scalarSlots scalar_injective]
    exact scalar_one n
  · rw [afterSquare,install_other widthSlots _ _ _ (by decide)]
    change install scalarSlots _ _ (scalarSlots 5)=_
    rw [install_slot scalarSlots scalar_injective]
    exact scalar_N n
  · rw [afterSquare,install_other widthSlots _ _ _ (by decide)]
    change install scalarSlots _ _ (scalarSlots 7)=_
    rw [install_slot scalarSlots scalar_injective]
    exact scalar_half n
  · rw [afterSquare,install_other widthSlots _ _ _ (by decide)]
    change install scalarSlots _ _ (scalarSlots 11)=_
    rw [install_slot scalarSlots scalar_injective]
    exact scalar_bits n
  · rw [afterSquare,install_other widthSlots _ _ _ (by decide)]
    change install scalarSlots _ _ (scalarSlots 28)=_
    rw [install_slot scalarSlots scalar_injective]
    exact scalar_counter n
  · rw [afterSquare,install_other widthSlots _ _ _ (by decide)]
    change install scalarSlots _ _ (scalarSlots 26)=_
    rw [install_slot scalarSlots scalar_injective]
    exact scalar_power n

theorem copy_target (C R n : Nat) (source : List Bool) (i : Fin 10) :
    afterSquare C R n source (copySlots (((i.castAdd 1).natAdd 10).castAdd 1))=[] := by
  have hw : ∀i:Fin 10,∀j,widthSlots j≠copySlots (((i.castAdd 1).natAdd 10).castAdd 1) := by decide
  have hs : ∀i:Fin 10,∀j,scalarSlots j≠copySlots (((i.castAdd 1).natAdd 10).castAdd 1) := by decide
  rw [afterSquare,install_other widthSlots _ _ _ (hw i),
    afterScalar,install_other scalarSlots _ _ _ (hs i)]
  fin_cases i <;>rfl

theorem copy_driver (C R n : Nat) (source : List Bool) :
    afterSquare C R n source (copySlots 20)=List.replicate (R^2) true := by
  change install widthSlots _ _ (widthSlots 5)=_
  rw [install_slot widthSlots width_injective]
  exact Width.raw_square R

theorem copy_log (C R n : Nat) (source : List Bool) :
    afterSquare C R n source (copySlots 21)=[] := by
  rw [afterSquare,install_other widthSlots _ _ _ (by decide),
    afterScalar,install_other scalarSlots _ _ _ (by decide)]
  rfl

theorem copy_input (C R n : Nat) (source : List Bool) (i : Fin 22) :
    afterSquare C R n source (copySlots i)=NativeFanout.input (m:=10) (palette C R (n+1)) (R^2) i := by
  refine Fin.addCases (m:=21) (n:=1) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=10) (n:=11) (fun k=>?_) (fun k=>?_) j
    · simpa only [NativeFanout.input,Fin.addCases_left] using copy_source C R n source k
    · refine Fin.addCases (m:=10) (n:=1) (fun k=>?_) (fun k=>?_) k
      · simpa only [NativeFanout.input,Fin.addCases_left,Fin.addCases_right] using copy_target C R n source k
      · fin_cases k
        exact copy_driver C R n source
  · fin_cases j
    exact copy_log C R n source

theorem copy_heads (i : Fin 22) : widthHeads (copySlots i)=0 := by
  have all : ∀i:Fin 22,widthHeads (copySlots i)=0 := by decide
  exact all i

theorem copy_run (C w n : Nat) (source : List Bool)
    (hN : n+1≤2^w) (hCodes : 2^(n+1)≤2^w) (hw : 1≤w) :
    Step copy (2*(commonReserve C w)^2+4) widthHeads
      (afterSquare C (commonReserve C w) n source) widthHeads
      (afterCopy C (commonReserve C w) n source) := by
  have h:=Step.of_ready (NativeFanout.ready identitySelect (palette C (commonReserve C w) (n+1))
    ((commonReserve C w)^2) (palette_length C w (n+1) hN hCodes hw))
  have hr:=Completion.SourceDock.dock h copySlots copy_injective widthHeads
    (afterSquare C (commonReserve C w) n source) copy_heads (copy_input C (commonReserve C w) n source)
  exact hr.congr (heads_existing copySlots widthHeads (fun _=>0) copy_heads) rfl

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Cold

import Proof.SourceAssembly.SourcePhaseRun

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourcePhase
open NearCubicWires.SourceParent
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

/-! ## 1. Slot values, every phase -/

section vals
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k r scratch : Nat)

theorem wd_val (ph : Phase) (j : Fin 278) :
    (Wd sources p k r scratch ph j).val =
      if j.val = 274 then PCJda54a286946142d3_BranchPhases.offset sources p k r + 126 + 2*(C10TailUniformSlots.phaseIndex ph).val
      else if j.val = 275 then PCJda54a286946142d3_BranchPhases.offset sources p k r + 127 + 2*(C10TailUniformSlots.phaseIndex ph).val
      else if j.val = 0 ∨ j.val = 1 ∨ j.val = 216 ∨ j.val = 217 ∨ (C10TailUniformSlots.phaseIndex ph).val = 0 then j.val
      else PCJda54a286946142d3_BranchPhases.offset sources p k r + 599 + ((C10TailUniformSlots.phaseIndex ph).val-1)*278 + j.val := by
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  simp only [Wd, CloseoutFinalC10RetainedPhaseFold.wordSlots, CloseoutFinalC10RetainedPhaseFold.tailSlots,
    CloseoutFinalC10RetainedPhaseFold.phaseBank]
  by_cases h274 : j.val = 274
  · have hw : (C10TailSlotsUniform.widthSlotT ph 0).val = 2 + 2*(C10TailUniformSlots.phaseIndex ph).val := rfl
    have hp := (C10TailUniformSlots.phaseIndex ph).isLt
    simp only [h274, if_true, hw]
    split_ifs <;> omega
  · by_cases h275 : j.val = 275
    · have hw : (C10TailSlotsUniform.widthSlotT ph 1).val = 2 + 2*(C10TailUniformSlots.phaseIndex ph).val + 1 := rfl
      have hp := (C10TailUniformSlots.phaseIndex ph).isLt
      simp only [h275, if_true, hw, if_neg (show ¬(275 = 274) by omega)]
      split_ifs <;> omega
    · simp only [if_neg h274, if_neg h275]
      split_ifs <;> simp_all

theorem fd_val (ph : Phase) (j : Fin 219) :
    (Fd sources p k r scratch ph j).val =
      if j.val = 215 then PCJda54a286946142d3_BranchPhases.offset sources p k r + 342 + (C10TailUniformSlots.phaseIndex ph).val
      else if j.val = 218 then PCJda54a286946142d3_BranchPhases.offset sources p k r + 132 + (C10TailUniformSlots.phaseIndex ph).val
      else if j.val = 0 ∨ j.val = 1 ∨ j.val = 216 ∨ j.val = 217 ∨ (C10TailUniformSlots.phaseIndex ph).val = 0 then j.val
      else PCJda54a286946142d3_BranchPhases.offset sources p k r + 599 + ((C10TailUniformSlots.phaseIndex ph).val-1)*278 + j.val := by
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have hp := (C10TailUniformSlots.phaseIndex ph).isLt
  simp only [Fd, CloseoutFinalC10RetainedPhaseFold.foldSlots, CloseoutFinalC10RetainedPhaseFold.tailSlots,
    CloseoutFinalC10RetainedPhaseFold.phaseBank]
  by_cases h215 : j.val = 215
  · have hs : (C10TailVerdict.scratchT ph).val = 218 + (C10TailUniformSlots.phaseIndex ph).val := by
      cases ph <;> rfl
    simp only [h215, if_true, hs]
    split_ifs <;> omega
  · by_cases h218 : j.val = 218
    · simp only [h218, if_true, if_neg (show ¬(218 = 215) by omega), Fin.val_mk]
      split_ifs <;> omega
    · simp only [if_neg h215, if_neg h218]
      split_ifs <;> simp_all

/-- A tape the phase's fold does not touch: off its word/fold slots, or one of its four protected
shared slots `0, 1, 216, 217`. -/
def FoldKeeps (ph : Phase) (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) : Prop :=
  ((∀ j, Wd sources p k r scratch ph j ≠ t) ∧ (∀ j, Fd sources p k r scratch ph j ≠ t)) ∨
    ∃ i : Fin 218, (i = 0 ∨ i = 1 ∨ i = 216 ∨ i = 217) ∧ t = Fd sources p k r scratch ph (i.castAdd 1)

theorem cache_cases (mode : Bool) (i : Fin 19) :
    (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i).val < 2 ∨
      (WorkspaceSelectedEntry.size sources k r p.clauseDegree ≤ (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i).val ∧
       (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i).val < PCJda54a286946142d3_BranchPhases.offset sources p k r) := by
  have hoff : PCJda54a286946142d3_BranchPhases.offset sources p k r =
      WorkspaceSelectedEntry.size sources k r p.clauseDegree + WorkspaceSelectedAdmission.originalTapes sources p k - 2 := rfl
  have hc := (WorkspaceSelectedEntryReady.cache sources p k mode i).isLt
  change (if (WorkspaceSelectedEntryReady.cache sources p k mode i).val<2 then
      (WorkspaceSelectedEntryReady.cache sources p k mode i).val else
      WorkspaceSelectedEntry.size sources k r p.clauseDegree+
        (WorkspaceSelectedEntryReady.cache sources p k mode i).val-2) < 2 ∨ _
  change _ ∨ (_ ≤ (if (WorkspaceSelectedEntryReady.cache sources p k mode i).val<2 then
      (WorkspaceSelectedEntryReady.cache sources p k mode i).val else
      WorkspaceSelectedEntry.size sources k r p.clauseDegree+
        (WorkspaceSelectedEntryReady.cache sources p k mode i).val-2) ∧
    (if (WorkspaceSelectedEntryReady.cache sources p k mode i).val<2 then
      (WorkspaceSelectedEntryReady.cache sources p k mode i).val else
      WorkspaceSelectedEntry.size sources k r p.clauseDegree+
        (WorkspaceSelectedEntryReady.cache sources p k mode i).val-2) < _)
  rw [hoff]
  split_ifs <;> omega

/-- A tape strictly between the penalty bank and the tail start is no word/fold slot of any phase. -/
theorem mid_keeps (ph : Phase) (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch))
    (h1 : 278 ≤ t.val) (h2 : t.val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 124) :
    FoldKeeps sources p k r scratch ph t := by
  left
  constructor
  · intro j he
    have hv := congrArg Fin.val he
    rw [wd_val] at hv
    have := j.isLt
    split_ifs at hv <;> omega
  · intro j he
    have hv := congrArg Fin.val he
    rw [fd_val] at hv
    have := j.isLt
    split_ifs at hv <;> omega

/-- Tapes 0 and 1 are protected fold slots of every phase. -/
theorem low_keeps (ph : Phase) (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch))
    (h : t.val < 2) : FoldKeeps sources p k r scratch ph t := by
  right
  refine ⟨⟨t.val, by omega⟩, ?_, ?_⟩
  · have : t.val = 0 ∨ t.val = 1 := by omega
    rcases this with h0 | h1
    · left; exact Fin.ext h0
    · right; left; exact Fin.ext h1
  · apply Fin.ext
    rw [fd_val]
    simp only [Fin.val_castAdd]
    split_ifs <;> omega

theorem cache_keeps (ph : Phase) (mode : Bool) (i : Fin 19) :
    FoldKeeps sources p k r scratch ph (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) := by
  have hP : 302 ≤ WorkspaceSelectedEntry.size sources k r p.clauseDegree := by
    unfold WorkspaceSelectedEntry.size; omega
  rcases cache_cases sources p k r scratch mode i with h | h
  · exact low_keeps sources p k r scratch ph _ h
  · exact mid_keeps sources p k r scratch ph _ (by omega) (by omega)

end vals

/-! ## 2. The realized exit on the body -/

section exit
variable {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {k den r scratch : Nat} {clock : OrdinaryClock (fun n => n^(k+2))} {n : Nat} {x : BitInput n}
    {oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)}
    {bits : List Bool}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {mode : Bool} {ph : Phase}
    {hin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → Nat}
    {tin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool}
    {fuel width : Nat}
    {code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}
    (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder)
    (w : PhaseWitness mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph hin tin fuel width code)

/-- The realized exit bank of a phase. -/
abbrev xA := (maskedBuildPhase mask selector packets rows compiler tables semantics buildSource sources p k den r scratch
  clock n x oracle bits site mode ph hin tin fuel width w.spec).realize.exit

/-- The realized exit heads of a phase. -/
abbrev xH := (maskedBuildPhase mask selector packets rows compiler tables semantics buildSource sources p k den r scratch
  clock n x oracle bits site mode ph hin tin fuel width w.spec).realize.heads

theorem exit_heads (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) :
    xH tables semantics buildSource w (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = w.H w.N t := by
  have e := (realize_exit tables semantics buildSource w).1
  change (maskedBuildPhase mask selector packets rows compiler tables semantics buildSource sources p k den r scratch
    clock n x oracle bits site mode ph hin tin fuel width w.spec).realize.heads _ = _
  rw [e]
  exact loopH_body w t

theorem exit_driverH :
    xH tables semantics buildSource w (PCJda54a286946142d3_BranchPhases.driver sources p k r scratch) = 1 := by
  have e := (realize_exit tables semantics buildSource w).1
  change (maskedBuildPhase mask selector packets rows compiler tables semantics buildSource sources p k den r scratch
    clock n x oracle bits site mode ph hin tin fuel width w.spec).realize.heads _ = _
  rw [e]
  exact loopH_driver w

theorem exit_driver :
    xA tables semantics buildSource w (PCJda54a286946142d3_BranchPhases.driver sources p k r scratch) =
      UnaryTemplate.tape w.N := by
  obtain ⟨out, e, _⟩ := (realize_exit tables semantics buildSource w).2
  change (maskedBuildPhase mask selector packets rows compiler tables semantics buildSource sources p k den r scratch
    clock n x oracle bits site mode ph hin tin fuel width w.spec).realize.exit _ = _
  rw [e, install_other _ _ _ _ (fun i he => PCJda54a286946142d3_BranchPhases.body_ne_driver sources p k r scratch i he)]
  exact loopA_driver w

theorem exit_frame (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch))
    (hW : ∀ j, Wd sources p k r scratch ph j ≠ t) (hF : ∀ j, Fd sources p k r scratch ph j ≠ t) :
    xA tables semantics buildSource w (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = w.A w.N t := by
  obtain ⟨out, e, _, _, _, _, hframe⟩ := (realize_exit tables semantics buildSource w).2
  change (maskedBuildPhase mask selector packets rows compiler tables semantics buildSource sources p k den r scratch
    clock n x oracle bits site mode ph hin tin fuel width w.spec).realize.exit _ = _
  rw [e, install_slot _ (PCJda54a286946142d3_BranchPhases.body_injective sources p k r scratch)]
  exact hframe t hW hF

theorem exit_protected (i : Fin 218) (hi : i = 0 ∨ i = 1 ∨ i = 216 ∨ i = 217) :
    xA tables semantics buildSource w (PCJda54a286946142d3_BranchPhases.body sources p k r scratch
      (Fd sources p k r scratch ph (i.castAdd 1))) = w.A w.N (Fd sources p k r scratch ph (i.castAdd 1)) := by
  obtain ⟨out, e, _, _, _, hprot, _⟩ := (realize_exit tables semantics buildSource w).2
  change (maskedBuildPhase mask selector packets rows compiler tables semantics buildSource sources p k den r scratch
    clock n x oracle bits site mode ph hin tin fuel width w.spec).realize.exit _ = _
  rw [e, install_slot _ (PCJda54a286946142d3_BranchPhases.body_injective sources p k r scratch)]
  exact hprot i hi

/-- The phase's two width words on its own tail slots, as the consumer states them. -/
theorem exit_words (j : Fin 2) :
    xA tables semantics buildSource w (PCJda54a286946142d3_BranchPhases.body sources p k r scratch
      (CloseoutFinalC10RetainedPhaseFold.tailSlots (PCJda54a286946142d3_BranchPhases.offset sources p k r)
        (ControllerSelectedContinuation.bodyTapes sources p k r scratch)
        (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r)
        (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch) (C10TailSlotsUniform.widthSlotT ph j))) =
      C10BodyWidths.widthWord width j := by
  obtain ⟨out, e, _, h274, h275, _, _⟩ := (realize_exit tables semantics buildSource w).2
  change (maskedBuildPhase mask selector packets rows compiler tables semantics buildSource sources p k den r scratch
    clock n x oracle bits site mode ph hin tin fuel width w.spec).realize.exit _ = _
  rw [e, install_slot _ (PCJda54a286946142d3_BranchPhases.body_injective sources p k r scratch), w.hwidth]
  have hw : CloseoutFinalC10WorkerFold.foldWidth (CompetitorRationalDecision.width w.b) w.entries =
      CloseoutFinalC10WorkerDock.joinScalarWidth w.b w.entries.length :=
    (CloseoutFinalC10WorkerDock.joinScalarWidth_eq w.b w.entries).symm
  rw [hw]
  fin_cases j
  · exact h274
  · exact h275

theorem exit_fold (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch))
    (ht : FoldKeeps sources p k r scratch ph t) :
    xA tables semantics buildSource w (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = w.A w.N t := by
  rcases ht with ⟨hW, hF⟩ | ⟨i, hi, rfl⟩
  · exact exit_frame tables semantics buildSource w t hW hF
  · exact exit_protected tables semantics buildSource w i hi

/-- With the per-clause exits: what the exit keeps from the loop start. -/
theorem exit_keep
    (exits : ∀ ci : Fin (NC sources k clock x oracle),
      SourceClauseExit mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
        site mode ph ci (w.H ci.val) (w.H (ci.val+1)) (w.A ci.val) (w.s_after ci.val) w.b w.siteFuel code (w.values ci))
    (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch))
    (hR : Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) t.val)
    (hc : ∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i)
    (h81 : t ≠ Wd sources p k r scratch ph 81) (h90 : t ≠ Wd sources p k r scratch ph 90)
    (ht : FoldKeeps sources p k r scratch ph t) :
    xA tables semantics buildSource w (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = w.A 0 t := by
  rw [exit_fold tables semantics buildSource w t ht]
  exact phase_keep w.H w.A w.s_after w.values exits w.s_next w.N (Nat.le_of_eq (N_eq_NC w.hN)) t hR hc h81 h90

theorem exit_keepH
    (exits : ∀ ci : Fin (NC sources k clock x oracle),
      SourceClauseExit mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
        site mode ph ci (w.H ci.val) (w.H (ci.val+1)) (w.A ci.val) (w.s_after ci.val) w.b w.siteFuel code (w.values ci))
    (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch))
    (hR : Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) t.val)
    (hc : ∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) :
    xH tables semantics buildSource w (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = w.H 0 t := by
  rw [exit_heads tables semantics buildSource w t]
  exact phase_keepH w.H w.A w.s_after w.values exits w.N (Nat.le_of_eq (N_eq_NC w.hN)) t hR hc

/-- The exit's query cache is at the end-of-loop state `clauseData N` (C3's premise). -/
theorem exit_cache (i : Fin 19) :
    xA tables semantics buildSource w (PCJda54a286946142d3_BranchPhases.body sources p k r scratch
      (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i)) =
      CD sources k clock x oracle (NC sources k clock x oracle) i := by
  have hkeep := cache_keeps sources p k r scratch ph mode i
  rw [exit_fold tables semantics buildSource w _ hkeep]
  have hNpos : 0 < w.N := by rw [w.hN]; exact Nat.two_pow_pos _
  have hN := N_eq_NC w.hN
  obtain ⟨m, hm⟩ : ∃ m, w.N = m+1 := ⟨w.N-1, by omega⟩
  rw [hm, w.s_next m (by omega), install_slot _ (PCJ30aa6f1b7c2a4221_.Selected.cache_injective sources p k r scratch mode)]
  rw [← hm, hN]

/-- The exit's cache heads are 0 (C3's premise). -/
theorem exit_cacheH (i : Fin 19) :
    xH tables semantics buildSource w (PCJda54a286946142d3_BranchPhases.body sources p k r scratch
      (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i)) = 0 := by
  rw [exit_heads tables semantics buildSource w]
  exact w.s_head w.N (Nat.le_of_eq (N_eq_NC w.hN)) i

end exit

end
end NearCubicWires.SourcePhase
end

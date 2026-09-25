import Proof.SourceAssembly.SourcePhaseLater

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

/-! ## 1. Tapes a phase passes through -/

section passes
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k r scratch : Nat)

/-- Tape `t` is in the phase region, off the cache, off the phase's append ports, kept by its fold. -/
def Passes (ph : Phase) (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) : Prop :=
  Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) t.val ∧ 2 ≤ t.val ∧ t ≠ Wd sources p k r scratch ph 81 ∧ t ≠ Wd sources p k r scratch ph 90 ∧
    FoldKeeps sources p k r scratch ph t

theorem passes_num (ph : Phase) (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (h278 : 278 ≤ t.val)
    (hR : t.val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 53 ∨ (PCJda54a286946142d3_BranchPhases.offset sources p k r + 124 ≤ t.val ∧ t.val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155))
    (hA : t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 126 + 2*(C10TailUniformSlots.phaseIndex ph).val) (hB : t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 127 + 2*(C10TailUniformSlots.phaseIndex ph).val)
    (hC : t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 342 + (C10TailUniformSlots.phaseIndex ph).val) (hD : t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 132 + (C10TailUniformSlots.phaseIndex ph).val)
    (hE : (C10TailUniformSlots.phaseIndex ph).val = 0 ∨ t.val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 599 + ((C10TailUniformSlots.phaseIndex ph).val-1)*278 ∨ PCJda54a286946142d3_BranchPhases.offset sources p k r + 599 + ((C10TailUniformSlots.phaseIndex ph).val-1)*278 + 278 ≤ t.val) :
    Passes sources p k r scratch ph t := by
  have e81 : (81 : Fin 278).val = 81 := rfl
  have e90 : (90 : Fin 278).val = 90 := rfl
  refine ⟨by unfold Region; omega, by omega, ?_, ?_, keeps_of sources p k r scratch ph t h278 hA hB hC hD hE⟩
  · intro he
    have hv := congrArg Fin.val he
    rcases wd_cases sources p k r scratch ph 81 with h | h | h | h <;> omega
  · intro he
    have hv := congrArg Fin.val he
    rcases wd_cases sources p k r scratch ph 90 with h | h | h | h <;> omega

theorem passes_217 (ph : Phase) (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (ht : t.val = 217) : Passes sources p k r scratch ph t := by
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have e81 : (81 : Fin 278).val = 81 := rfl
  have e90 : (90 : Fin 278).val = 90 := rfl
  refine ⟨by unfold Region; omega, by omega, ?_, ?_, keeps_217 sources p k r scratch ph t ht⟩
  · intro he
    have hv := congrArg Fin.val he
    rcases wd_cases sources p k r scratch ph 81 with h | h | h | h <;> omega
  · intro he
    have hv := congrArg Fin.val he
    rcases wd_cases sources p k r scratch ph 90 with h | h | h | h <;> omega

theorem tl_val (i : Fin 475) : (CloseoutFinalC10RetainedPhaseFold.tailSlots (PCJda54a286946142d3_BranchPhases.offset sources p k r) (ControllerSelectedContinuation.bodyTapes sources p k r scratch) (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r) (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch) i).val = if i.val = 473 then 217 else PCJda54a286946142d3_BranchPhases.offset sources p k r + 124 + i.val := rfl

theorem term_val : (PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 53 := rfl

theorem term_region : Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) (PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch).val := Or.inr (Or.inl rfl)

end passes

/-! ## 2. The realized exit on passing tapes -/

theorem passA {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {k den r scratch : Nat} {clock : OrdinaryClock (fun n => n^(k+2))} {n : Nat} {x : BitInput n}
    {oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)}
    {bits : List Bool} {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {mode : Bool} {ph : Phase} {hin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → Nat} {tin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool} {fuel width : Nat}
    {code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph} (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder)
    (w : PhaseWitness mask selector packets rows compiler sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width code) (exits : ∀ ci : Fin (NC sources k clock x oracle), SourceClauseExit mask selector packets rows compiler sources p k den r scratch clock n x oracle bits site mode ph ci (w.H ci.val) (w.H (ci.val+1)) (w.A ci.val) (w.s_after ci.val) w.b w.siteFuel code (w.values ci))
    (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (h : Passes sources p k r scratch ph t) : xA tables semantics buildSource w (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = w.A 0 t :=
  exit_keep tables semantics buildSource w exits t h.1 (not_cache sources p k r scratch mode t h.2.1 h.1)
    h.2.2.1 h.2.2.2.1 h.2.2.2.2

theorem later_passA {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {k den r scratch : Nat} {clock : OrdinaryClock (fun n => n^(k+2))} {n : Nat} {x : BitInput n}
    {oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)}
    {bits : List Bool} {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {mode : Bool} {ph : Phase} {hin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → Nat} {tin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool} {fuel width : Nat}
    {code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph} (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder)
    (w : PhaseWitness mask selector packets rows compiler sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width code) (exits : ∀ ci : Fin (NC sources k clock x oracle), SourceClauseExit mask selector packets rows compiler sources p k den r scratch clock n x oracle bits site mode ph ci (w.H ci.val) (w.H (ci.val+1)) (w.A ci.val) (w.s_after ci.val) w.b w.siteFuel code (w.values ci))
    (hA0 : ∀ t, (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) → w.A 0 t = tin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (h : Passes sources p k r scratch ph t) : xA tables semantics buildSource w (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = tin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) := by
  rw [passA tables semantics buildSource w exits t h]
  exact hA0 t (not_cache sources p k r scratch mode t h.2.1 h.1)

theorem heads_zero {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {k den r scratch : Nat} {clock : OrdinaryClock (fun n => n^(k+2))} {n : Nat} {x : BitInput n}
    {oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)}
    {bits : List Bool} {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {mode : Bool} {ph : Phase} {hin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → Nat} {tin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool} {fuel width : Nat}
    {code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph} (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder)
    (w : PhaseWitness mask selector packets rows compiler sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width code) (exits : ∀ ci : Fin (NC sources k clock x oracle), SourceClauseExit mask selector packets rows compiler sources p k den r scratch clock n x oracle bits site mode ph ci (w.H ci.val) (w.H (ci.val+1)) (w.A ci.val) (w.s_after ci.val) w.b w.siteFuel code (w.values ci))
    (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (hR : Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) t.val) (h0 : (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) → w.H 0 t = 0) :
    xH tables semantics buildSource w (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = 0 := by
  by_cases hc : ∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i
  · rw [exit_keepH tables semantics buildSource w exits t hR hc]
    exact h0 hc
  · obtain ⟨i, hi⟩ := not_forall.mp hc
    rw [not_not.mp hi]
    exact exit_cacheH tables semantics buildSource w i

theorem later_heads {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {k den r scratch : Nat} {clock : OrdinaryClock (fun n => n^(k+2))} {n : Nat} {x : BitInput n}
    {oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)}
    {bits : List Bool} {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {mode : Bool} {ph : Phase} {hin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → Nat} {tin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool} {fuel width : Nat}
    {code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph} (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder)
    (w : PhaseWitness mask selector packets rows compiler sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width code) (exits : ∀ ci : Fin (NC sources k clock x oracle), SourceClauseExit mask selector packets rows compiler sources p k den r scratch clock n x oracle bits site mode ph ci (w.H ci.val) (w.H (ci.val+1)) (w.A ci.val) (w.s_after ci.val) w.b w.siteFuel code (w.values ci))
    (hH0 : ∀ t, w.H 0 t = hin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (hR : Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) t.val) (h2 : 2 ≤ t.val) :
    xH tables semantics buildSource w (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = hin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) := by
  rw [exit_keepH tables semantics buildSource w exits t hR (not_cache sources p k r scratch mode t h2 hR)]
  exact hH0 t

theorem exit_driverT {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {k den r scratch : Nat} {clock : OrdinaryClock (fun n => n^(k+2))} {n : Nat} {x : BitInput n}
    {oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)}
    {bits : List Bool} {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {mode : Bool} {ph : Phase} {hin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → Nat} {tin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool} {fuel width : Nat}
    {code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph} (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder)
    (w : PhaseWitness mask selector packets rows compiler sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width code) :
    xA tables semantics buildSource w (PCJda54a286946142d3_BranchPhases.driver sources p k r scratch) = UnaryTemplate.tape (NC sources k clock x oracle) := by
  rw [exit_driver tables semantics buildSource w, N_eq_NC w.hN]

/-! ## 3. The ready bank, restated -/

section bank
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
  (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
  (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)

theorem pen_low (j : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (h2 : 2 ≤ j.val) (h278 : j.val < 278) (h90 : j.val ≠ 90) (h216 : j.val ≠ 216)
    (h218 : j.val ≠ 218) : (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j) = [] :=
  (penalty_bank sources p den hden k r scratch n x bits hp).2.1 j h2 h278 h90 h216 h218

theorem pen_far (j : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (h : PCJda54a286946142d3_BranchPhases.offset sources p k r + 96 ≤ j.val) : (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j) = [] :=
  (penalty_bank sources p den hden k r scratch n x bits hp).2.2.2.2.2.1 j h

theorem pen_term : (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch)) = List.replicate (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) true :=
  (penalty_bank sources p den hden k r scratch n x bits hp).2.2.2.2.1

include hp in
theorem pen_heads (j : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (h : j.val ≠ WorkspaceSelectedEntry.size sources k r p.clauseDegree - 1) : (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j) = 0 :=
  (penalty_bank sources p den hden k r scratch n x bits hp).2.2.2.2.2.2.2.2.1 j h

include hp in
theorem pen_heads_num (j : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (h : j.val < 278 ∨ PCJda54a286946142d3_BranchPhases.offset sources p k r ≤ j.val) : (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j) = 0 := by
  have hP := size_302 sources p k r
  have hoff : PCJda54a286946142d3_BranchPhases.offset sources p k r = WorkspaceSelectedEntry.size sources k r p.clauseDegree + WorkspaceSelectedAdmission.originalTapes sources p k - 2 := rfl
  have ht := WorkspaceSelectedEntryReady.old_size sources p k
  apply pen_heads sources p den hden k r scratch n x bits hp j
  omega

end bank

/-! ## 4. The penalty exit is a later entry bank -/

theorem pen_blank {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den : Nat} {hden : 0 < den} {k r scratch n : Nat} {x : BitInput n} {bits : List Bool}
    {hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}
    {cost width : Phase → Nat} (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder) (wp : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) (code .penalty))
    (ep : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty ci (wp.H ci.val) (wp.H (ci.val+1)) (wp.A ci.val) (wp.s_after ci.val) wp.b wp.siteFuel (code .penalty) (wp.values ci))
    (hAp : ∀ t, wp.A 0 t = penaltyA0 sources p den hden k r scratch n x bits hp t) (hHp : ∀ t, wp.H 0 t = (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (hP : Passes sources p k r scratch .penalty t) (h96 : PCJda54a286946142d3_BranchPhases.offset sources p k r + 96 ≤ t.val)
    (hoffs : t.val ≠ 218 ∧ (t.val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 124 ∨
      (t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 124 ∧ t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 125 ∧ t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 135 ∧ t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 136 ∧
       t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 137 ∧ t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 689 ∧ t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 817 ∧ t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 967 ∧
       t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 1095))) :
    xA tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = [] := by
  rw [passA tables semantics buildSource wp ep t hP, hAp,
    penaltyA0_off sources p den hden k r scratch n x bits hp t hoffs]
  exact pen_far sources p den hden k r scratch n x bits hp t h96

theorem pen_fslot {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den : Nat} {hden : 0 < den} {k r scratch n : Nat} {x : BitInput n} {bits : List Bool}
    {hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}
    {cost width : Phase → Nat} (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder) (wp : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) (code .penalty))
    (ep : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty ci (wp.H ci.val) (wp.H (ci.val+1)) (wp.A ci.val) (wp.s_after ci.val) wp.b wp.siteFuel (code .penalty) (wp.values ci))
    (hAp : ∀ t, wp.A 0 t = penaltyA0 sources p den hden k r scratch n x bits hp t) (hHp : ∀ t, wp.H 0 t = (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (j : Fin 10) (hP : Passes sources p k r scratch .penalty (fSlots sources p k r scratch j)) :
    xA tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (fSlots sources p k r scratch j)) = firstLocal (C10PartsSchedule.entryWidthSchedule sources k r n) j := by
  rw [passA tables semantics buildSource wp ep _ hP, hAp]
  unfold penaltyA0
  exact install_slot _ (CloseoutFinalC10FirstPhaseEntry.slots_injective _ _ _ _) _ _ j

theorem pen_passes (ph : Phase) (hph : ph = .moment ∨ ph = .clause) (sources : EightSources) {gamma : Real}
    (p : Parameters sources gamma) (k r scratch : Nat) (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch))
    (h : t.val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 53 ∨ (PCJda54a286946142d3_BranchPhases.offset sources p k r + 128 ≤ t.val ∧ t.val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 ∧ t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 342 ∧ t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 132)) :
    Passes sources p k r scratch .penalty t := by
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have d0 : (C10TailUniformSlots.phaseIndex Phase.penalty).val = 0 := rfl
  apply passes_num sources p k r scratch .penalty t <;> omega

theorem wd_later (ph : Phase) (hph : ph = .moment ∨ ph = .clause) (sources : EightSources) {gamma : Real}
    (p : Parameters sources gamma) (k r scratch : Nat) (i : Fin 278) (h2 : 2 ≤ i.val) (h216 : i.val ≠ 216)
    (h217 : i.val ≠ 217) :
    ((Wd sources p k r scratch ph i).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 128 + 2*((C10TailUniformSlots.phaseIndex ph).val-1) + (i.val - 274) ∧ (i.val = 274 ∨ i.val = 275)) ∨
    ((Wd sources p k r scratch ph i).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 599 + ((C10TailUniformSlots.phaseIndex ph).val-1)*278 + i.val ∧ i.val ≠ 274 ∧ i.val ≠ 275) := by
  have hd : (C10TailUniformSlots.phaseIndex ph).val = 1 ∨ (C10TailUniformSlots.phaseIndex ph).val = 2 := by
    rcases hph with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases wd_cases sources p k r scratch ph i with h | h | h | h <;> omega

theorem fd_later (ph : Phase) (hph : ph = .moment ∨ ph = .clause) (sources : EightSources) {gamma : Real}
    (p : Parameters sources gamma) (k r scratch : Nat) :
    (Fd sources p k r scratch ph 215).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 342 + (C10TailUniformSlots.phaseIndex ph).val ∧
    (Fd sources p k r scratch ph 218).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 132 + (C10TailUniformSlots.phaseIndex ph).val ∧ ((C10TailUniformSlots.phaseIndex ph).val = 1 ∨ (C10TailUniformSlots.phaseIndex ph).val = 2) := by
  have hd : (C10TailUniformSlots.phaseIndex ph).val = 1 ∨ (C10TailUniformSlots.phaseIndex ph).val = 2 := by
    rcases hph with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have e215 : (215 : Fin 219).val = 215 := rfl
  have e218 : (218 : Fin 219).val = 218 := rfl
  refine ⟨?_, ?_, hd⟩
  · rcases fd_cases sources p k r scratch ph 215 with h | h | h | h <;> omega
  · rcases fd_cases sources p k r scratch ph 218 with h | h | h | h <;> omega

theorem pen_later_tapes {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den : Nat} {hden : 0 < den} {k r scratch n : Nat} {x : BitInput n} {bits : List Bool}
    {hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}
    {cost width : Phase → Nat} (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder) (wp : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) (code .penalty))
    (ep : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty ci (wp.H ci.val) (wp.H (ci.val+1)) (wp.A ci.val) (wp.s_after ci.val) wp.b wp.siteFuel (code .penalty) (wp.values ci))
    (hAp : ∀ t, wp.A 0 t = penaltyA0 sources p den hden k r scratch n x bits hp t) (hHp : ∀ t, wp.H 0 t = (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (ph : Phase) (hph : ph = .moment ∨ ph = .clause) :
    (∀ i : Fin 278, 2 ≤ i.val → i.val < 215 → i.val ≠ 81 → i.val ≠ 90 →
      xA tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Wd sources p k r scratch ph i)) = []) ∧
    (∀ i : Fin 278, 219 ≤ i.val → xA tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Wd sources p k r scratch ph i)) = []) ∧
    xA tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Fd sources p k r scratch ph 215)) = [] ∧
    xA tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Fd sources p k r scratch ph 218)) = [] ∧
    xA tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Wd sources p k r scratch ph 81)) = [] := by
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have hF := PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch
  obtain ⟨f215, f218, hd⟩ := fd_later ph hph sources p k r scratch
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i h2 h3 h4 h5
    have hi := i.isLt
    rcases wd_later ph hph sources p k r scratch i h2 (by omega) (by omega) with h | h
    · omega
    · exact pen_blank tables semantics buildSource wp ep hAp hHp _
        (pen_passes ph hph sources p k r scratch _ (by omega)) (by omega) (by omega)
  · intro i h2
    have hi := i.isLt
    rcases wd_later ph hph sources p k r scratch i (by omega) (by omega) (by omega) with h | h
    · exact pen_blank tables semantics buildSource wp ep hAp hHp _
        (pen_passes ph hph sources p k r scratch _ (by omega)) (by omega) (by omega)
    · exact pen_blank tables semantics buildSource wp ep hAp hHp _
        (pen_passes ph hph sources p k r scratch _ (by omega)) (by omega) (by omega)
  · exact pen_blank tables semantics buildSource wp ep hAp hHp _
      (pen_passes ph hph sources p k r scratch _ (by omega)) (by omega) (by omega)
  · exact pen_blank tables semantics buildSource wp ep hAp hHp _
      (pen_passes ph hph sources p k r scratch _ (by omega)) (by omega) (by omega)
  · have e81 : (81 : Fin 278).val = 81 := rfl
    rcases wd_later ph hph sources p k r scratch 81 (by omega) (by omega) (by omega) with h | h
    · omega
    · exact pen_blank tables semantics buildSource wp ep hAp hHp _
        (pen_passes ph hph sources p k r scratch _ (by omega)) (by omega) (by omega)

theorem fslot_vals (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k r scratch : Nat) :
    (fSlots sources p k r scratch 2).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 817 ∧ (fSlots sources p k r scratch 4).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 1095 ∧
    (fSlots sources p k r scratch 6).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 689 ∧ (fSlots sources p k r scratch 8).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 967 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [fSlots, CloseoutFinalC10FirstPhaseEntry.firstSlots]

theorem wd_fslot (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k r scratch : Nat) :
    Wd sources p k r scratch .moment 218 = fSlots sources p k r scratch 2 ∧
    Wd sources p k r scratch .clause 218 = fSlots sources p k r scratch 4 ∧
    Wd sources p k r scratch .moment 90 = fSlots sources p k r scratch 6 ∧
    Wd sources p k r scratch .clause 90 = fSlots sources p k r scratch 8 := by
  obtain ⟨f2, f4, f6, f8⟩ := fslot_vals sources p k r scratch
  have e218 : (218 : Fin 278).val = 218 := rfl
  have e90 : (90 : Fin 278).val = 90 := rfl
  have d1 : (C10TailUniformSlots.phaseIndex Phase.moment).val = 1 := rfl
  have d2 : (C10TailUniformSlots.phaseIndex Phase.clause).val = 2 := rfl
  refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩
  · rw [f2]
    rcases wd_cases sources p k r scratch .moment 218 with h | h | h | h <;> omega
  · rw [f4]
    rcases wd_cases sources p k r scratch .clause 218 with h | h | h | h <;> omega
  · rw [f6]
    rcases wd_cases sources p k r scratch .moment 90 with h | h | h | h <;> omega
  · rw [f8]
    rcases wd_cases sources p k r scratch .clause 90 with h | h | h | h <;> omega

theorem pen_later_words {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den : Nat} {hden : 0 < den} {k r scratch n : Nat} {x : BitInput n} {bits : List Bool}
    {hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}
    {cost width : Phase → Nat} (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder) (wp : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) (code .penalty))
    (ep : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty ci (wp.H ci.val) (wp.H (ci.val+1)) (wp.A ci.val) (wp.s_after ci.val) wp.b wp.siteFuel (code .penalty) (wp.values ci))
    (hAp : ∀ t, wp.A 0 t = penaltyA0 sources p den hden k r scratch n x bits hp t) (hHp : ∀ t, wp.H 0 t = (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (ph : Phase) (hph : ph = .moment ∨ ph = .clause) :
    xA tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Wd sources p k r scratch ph 218)) = List.replicate (C10PartsSchedule.entryWidthSchedule sources k r n) true ∧
    xA tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Wd sources p k r scratch ph 90)) = CompareMachine.word 0 := by
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have hF := PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch
  obtain ⟨m218, c218, m90, c90⟩ := wd_fslot sources p k r scratch
  have spec := firstLocal_spec (C10PartsSchedule.entryWidthSchedule sources k r n)
  obtain ⟨f2, f4, f6, f8⟩ := fslot_vals sources p k r scratch
  have fv : ∀ j : Fin 10, (j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 8) →
      Passes sources p k r scratch .penalty (fSlots sources p k r scratch j) := by
    intro j hj
    apply pen_passes .moment (Or.inl rfl) sources p k r scratch
    rcases hj with rfl | rfl | rfl | rfl
    · rw [f2]; omega
    · rw [f4]; omega
    · rw [f6]; omega
    · rw [f8]; omega
  rcases hph with rfl | rfl
  · rw [m218, m90, pen_fslot tables semantics buildSource wp ep hAp hHp 2 (fv 2 (by decide)),
      pen_fslot tables semantics buildSource wp ep hAp hHp 6 (fv 6 (by decide))]
    exact ⟨spec.2.2.2.1, spec.2.2.2.2.2.1⟩
  · rw [c218, c90, pen_fslot tables semantics buildSource wp ep hAp hHp 4 (fv 4 (by decide)),
      pen_fslot tables semantics buildSource wp ep hAp hHp 8 (fv 8 (by decide))]
    exact ⟨spec.2.2.2.2.1, spec.2.2.2.2.2.2⟩

theorem pen_later_heads {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den : Nat} {hden : 0 < den} {k r scratch n : Nat} {x : BitInput n} {bits : List Bool}
    {hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}
    {cost width : Phase → Nat} (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder) (wp : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) (code .penalty))
    (ep : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty ci (wp.H ci.val) (wp.H (ci.val+1)) (wp.A ci.val) (wp.s_after ci.val) wp.b wp.siteFuel (code .penalty) (wp.values ci))
    (hAp : ∀ t, wp.A 0 t = penaltyA0 sources p den hden k r scratch n x bits hp t) (hHp : ∀ t, wp.H 0 t = (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (hR : Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) t.val) (h : t.val < 278 ∨ PCJda54a286946142d3_BranchPhases.offset sources p k r ≤ t.val) :
    xH tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = 0 :=
  heads_zero tables semantics buildSource wp ep t hR (fun _ => by
    rw [hHp]; exact pen_heads_num sources p den hden k r scratch n x bits hp t h)

theorem pen_termA {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den : Nat} {hden : 0 < den} {k r scratch n : Nat} {x : BitInput n} {bits : List Bool}
    {hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}
    {cost width : Phase → Nat} (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder) (wp : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) (code .penalty))
    (ep : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty ci (wp.H ci.val) (wp.H (ci.val+1)) (wp.A ci.val) (wp.s_after ci.val) wp.b wp.siteFuel (code .penalty) (wp.values ci))
    (hAp : ∀ t, wp.A 0 t = penaltyA0 sources p den hden k r scratch n x bits hp t) (hHp : ∀ t, wp.H 0 t = (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t)) :
    xA tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch)) = List.replicate (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) true := by
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have tv := term_val sources p k r scratch
  rw [passA tables semantics buildSource wp ep _ (pen_passes .moment (Or.inl rfl) sources p k r scratch _ (Or.inl tv)), hAp,
    penaltyA0_off sources p den hden k r scratch n x bits hp _ (by omega)]
  exact pen_term sources p den hden k r scratch n x bits hp

/-- **The penalty exit is the entry bank both later phases need.** -/
theorem pen_later {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den : Nat} {hden : 0 < den} {k r scratch n : Nat} {x : BitInput n} {bits : List Bool}
    {hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}
    {cost width : Phase → Nat} (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder) (wp : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) (code .penalty))
    (ep : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty ci (wp.H ci.val) (wp.H (ci.val+1)) (wp.A ci.val) (wp.s_after ci.val) wp.b wp.siteFuel (code .penalty) (wp.values ci))
    (hAp : ∀ t, wp.A 0 t = penaltyA0 sources p den hden k r scratch n x bits hp t) (hHp : ∀ t, wp.H 0 t = (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (ph : Phase) (hph : ph = .moment ∨ ph = .clause) :
    LaterIn sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) ph (C10PartsSchedule.entryWidthSchedule sources k r n) (xH tables semantics buildSource wp) (xA tables semantics buildSource wp) := by
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have hF := PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch
  obtain ⟨T1, T2, T3, T4, T5⟩ := pen_later_tapes tables semantics buildSource wp ep hAp hHp ph hph
  obtain ⟨W1, W2⟩ := pen_later_words tables semantics buildSource wp ep hAp hHp ph hph
  have tv := term_val sources p k r scratch
  exact {
    blank := T1
    fresh := T2
    record := T3
    log := T4
    driver := W1
    stream := T5
    count := W2
    cache := exit_cache tables semantics buildSource wp
    cacheH := exit_cacheH tables semantics buildSource wp
    termH := pen_later_heads tables semantics buildSource wp ep hAp hHp _ (term_region sources p k r scratch) (by omega)
    countT := pen_termA tables semantics buildSource wp ep hAp hHp
    Hw := fun i => pen_later_heads tables semantics buildSource wp ep hAp hHp _
      (wordSlots_region _ _ _ _ ph i) (by rcases wd_cases sources p k r scratch ph i with h | h | h | h <;> omega)
    Hf := fun i => pen_later_heads tables semantics buildSource wp ep hAp hHp _
      (foldSlots_region _ _ _ _ ph i) (by rcases fd_cases sources p k r scratch ph i with h | h | h | h <;> omega)
    driverH := exit_driverH tables semantics buildSource wp
    driverT := exit_driverT tables semantics buildSource wp }

/-! ## 5. The moment phase carries the clause phase's entry bank through -/

theorem mom_passes (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k r scratch : Nat)
    (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch))
    (h : t.val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 53 ∨ (PCJda54a286946142d3_BranchPhases.offset sources p k r + 124 ≤ t.val ∧ t.val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 599 ∧ t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 128 ∧ t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 129 ∧
      t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 343 ∧ t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 133) ∨ (PCJda54a286946142d3_BranchPhases.offset sources p k r + 877 ≤ t.val ∧ t.val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155)) :
    Passes sources p k r scratch .moment t := by
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have d1 : (C10TailUniformSlots.phaseIndex Phase.moment).val = 1 := rfl
  apply passes_num sources p k r scratch .moment t <;> omega

theorem cl_passes (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k r scratch : Nat)
    (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch))
    (h : t.val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 53 ∨ (PCJda54a286946142d3_BranchPhases.offset sources p k r + 124 ≤ t.val ∧ t.val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 877 ∧ t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 130 ∧ t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 131 ∧
      t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 344 ∧ t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 134)) :
    Passes sources p k r scratch .clause t := by
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have d2 : (C10TailUniformSlots.phaseIndex Phase.clause).val = 2 := rfl
  apply passes_num sources p k r scratch .clause t <;> omega

theorem later_pass {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {k den r scratch : Nat} {clock : OrdinaryClock (fun n => n^(k+2))} {n : Nat} {x : BitInput n}
    {oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)}
    {bits : List Bool} {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {mode : Bool} {hin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → Nat} {tin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool} {fuel width b : Nat}
    {code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch .moment}
    (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder)
    (w : PhaseWitness mask selector packets rows compiler sources p k den r scratch clock n x oracle bits site mode .moment hin tin fuel width code) (exits : ∀ ci : Fin (NC sources k clock x oracle), SourceClauseExit mask selector packets rows compiler sources p k den r scratch clock n x oracle bits site mode .moment ci (w.H ci.val) (w.H (ci.val+1)) (w.A ci.val) (w.s_after ci.val) w.b w.siteFuel code (w.values ci))
    (hA0 : ∀ t, (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) → w.A 0 t = tin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (hH0 : ∀ t, w.H 0 t = hin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (hI : LaterIn sources p k r scratch clock x oracle mode .clause b hin tin) :
    LaterIn sources p k r scratch clock x oracle mode .clause b (xH tables semantics buildSource w) (xA tables semantics buildSource w) := by
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have hF := PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch
  have tv := term_val sources p k r scratch
  obtain ⟨f215, f218, -⟩ := fd_later .clause (Or.inr rfl) sources p k r scratch
  have d2 : (C10TailUniformSlots.phaseIndex Phase.clause).val = 2 := rfl
  have pass := later_passA tables semantics buildSource w exits hA0
  have e81 : (81 : Fin 278).val = 81 := rfl
  have e90 : (90 : Fin 278).val = 90 := rfl
  have e218 : (218 : Fin 278).val = 218 := rfl
  refine {
    blank := ?_
    fresh := ?_
    record := ?_
    log := ?_
    driver := ?_
    stream := ?_
    count := ?_
    cache := exit_cache tables semantics buildSource w
    cacheH := exit_cacheH tables semantics buildSource w
    termH := ?_
    countT := ?_
    Hw := ?_
    Hf := ?_
    driverH := exit_driverH tables semantics buildSource w
    driverT := exit_driverT tables semantics buildSource w }
  · intro i h2 h3 h4 h5
    have hi := i.isLt
    rcases wd_later .clause (Or.inr rfl) sources p k r scratch i h2 (by omega) (by omega) with h | h
    · omega
    · rw [pass _ (mom_passes sources p k r scratch _ (by omega))]; exact hI.blank i h2 h3 h4 h5
  · intro i h2
    have hi := i.isLt
    rcases wd_later .clause (Or.inr rfl) sources p k r scratch i (by omega) (by omega) (by omega) with h | h
    · rw [pass _ (mom_passes sources p k r scratch _ (by omega))]; exact hI.fresh i h2
    · rw [pass _ (mom_passes sources p k r scratch _ (by omega))]; exact hI.fresh i h2
  · rw [pass _ (mom_passes sources p k r scratch _ (by omega))]; exact hI.record
  · rw [pass _ (mom_passes sources p k r scratch _ (by omega))]; exact hI.log
  · rcases wd_later .clause (Or.inr rfl) sources p k r scratch 218 (by omega) (by omega) (by omega) with h | h
    · omega
    · rw [pass _ (mom_passes sources p k r scratch _ (by omega))]; exact hI.driver
  · rcases wd_later .clause (Or.inr rfl) sources p k r scratch 81 (by omega) (by omega) (by omega) with h | h
    · omega
    · rw [pass _ (mom_passes sources p k r scratch _ (by omega))]; exact hI.stream
  · rcases wd_later .clause (Or.inr rfl) sources p k r scratch 90 (by omega) (by omega) (by omega) with h | h
    · omega
    · rw [pass _ (mom_passes sources p k r scratch _ (by omega))]; exact hI.count
  · rw [later_heads tables semantics buildSource w exits hH0 _ (term_region sources p k r scratch) (by omega)]
    exact hI.termH
  · rw [pass _ (mom_passes sources p k r scratch _ (Or.inl tv))]; exact hI.countT
  · intro i
    exact heads_zero tables semantics buildSource w exits _ (wordSlots_region _ _ _ _ .clause i)
      (fun _ => by rw [hH0]; exact hI.Hw i)
  · intro i
    exact heads_zero tables semantics buildSource w exits _ (foldSlots_region _ _ _ _ .clause i)
      (fun _ => by rw [hH0]; exact hI.Hf i)

/-! ## 6. J2 and J4 -/

theorem chainA {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den : Nat} {hden : 0 < den} {k r scratch n : Nat} {x : BitInput n} {bits : List Bool}
    {hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}
    {cost width : Phase → Nat} (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder) (wp : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) (code .penalty))
    (ep : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty ci (wp.H ci.val) (wp.H (ci.val+1)) (wp.A ci.val) (wp.s_after ci.val) wp.b wp.siteFuel (code .penalty) (wp.values ci))
    (hAp : ∀ t, wp.A 0 t = penaltyA0 sources p den hden k r scratch n x bits hp t) (hHp : ∀ t, wp.H 0 t = (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (wm : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .moment (xH tables semantics buildSource wp) (xA tables semantics buildSource wp) (cost .moment) (width .moment) (code .moment))
    (em : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .moment ci (wm.H ci.val) (wm.H (ci.val+1)) (wm.A ci.val) (wm.s_after ci.val) wm.b wm.siteFuel (code .moment) (wm.values ci))
    (hAm : ∀ t, (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) → wm.A 0 t = xA tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t)) (hHm : ∀ t, wm.H 0 t = xH tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (wc : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .clause (xH tables semantics buildSource wm) (xA tables semantics buildSource wm) (cost .clause) (width .clause) (code .clause))
    (ec : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .clause ci (wc.H ci.val) (wc.H (ci.val+1)) (wc.A ci.val) (wc.s_after ci.val) wc.b wc.siteFuel (code .clause) (wc.values ci))
    (hAc : ∀ t, (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) → wc.A 0 t = xA tables semantics buildSource wm (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t)) (hHc : ∀ t, wc.H 0 t = xH tables semantics buildSource wm (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (Pc : Passes sources p k r scratch .clause t) (Pm : Passes sources p k r scratch .moment t) :
    xA tables semantics buildSource wc (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = xA tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) := by
  rw [later_passA tables semantics buildSource wc ec hAc t Pc, later_passA tables semantics buildSource wm em hAm t Pm]

theorem j2_pen {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den : Nat} {hden : 0 < den} {k r scratch n : Nat} {x : BitInput n} {bits : List Bool}
    {hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}
    {cost width : Phase → Nat} (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder) (wp : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) (code .penalty))
    (ep : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty ci (wp.H ci.val) (wp.H (ci.val+1)) (wp.A ci.val) (wp.s_after ci.val) wp.b wp.siteFuel (code .penalty) (wp.values ci))
    (hAp : ∀ t, wp.A 0 t = penaltyA0 sources p den hden k r scratch n x bits hp t) (hHp : ∀ t, wp.H 0 t = (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (wm : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .moment (xH tables semantics buildSource wp) (xA tables semantics buildSource wp) (cost .moment) (width .moment) (code .moment))
    (em : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .moment ci (wm.H ci.val) (wm.H (ci.val+1)) (wm.A ci.val) (wm.s_after ci.val) wm.b wm.siteFuel (code .moment) (wm.values ci))
    (hAm : ∀ t, (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) → wm.A 0 t = xA tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t)) (hHm : ∀ t, wm.H 0 t = xH tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (wc : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .clause (xH tables semantics buildSource wm) (xA tables semantics buildSource wm) (cost .clause) (width .clause) (code .clause))
    (ec : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .clause ci (wc.H ci.val) (wc.H (ci.val+1)) (wc.A ci.val) (wc.s_after ci.val) wc.b wc.siteFuel (code .clause) (wc.values ci))
    (hAc : ∀ t, (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) → wc.A 0 t = xA tables semantics buildSource wm (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t)) (hHc : ∀ t, wc.H 0 t = xH tables semantics buildSource wm (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t)) :
    xA tables semantics buildSource wc (PCJ374c44bb8b7f47d9_.S.ports sources p k r scratch .penalty) =
      xA tables semantics buildSource wp (PCJ374c44bb8b7f47d9_.S.ports sources p k r scratch .penalty) := by
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have sv : (C10TailVerdict.scratchT .penalty).val = 218 := rfl
  have tv : (CloseoutFinalC10RetainedPhaseFold.tailSlots (PCJda54a286946142d3_BranchPhases.offset sources p k r) (ControllerSelectedContinuation.bodyTapes sources p k r scratch) (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r) (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch) (C10TailVerdict.scratchT .penalty)).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 342 := by
    rw [tl_val, sv, if_neg (by decide)]
  exact chainA tables semantics buildSource wp ep hAp hHp wm em hAm hHm wc ec hAc hHc _
    (cl_passes sources p k r scratch _ (by omega)) (mom_passes sources p k r scratch _ (by omega))

theorem j2_mom {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den : Nat} {hden : 0 < den} {k r scratch n : Nat} {x : BitInput n} {bits : List Bool}
    {hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}
    {cost width : Phase → Nat} (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder) (wp : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) (code .penalty))
    (ep : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty ci (wp.H ci.val) (wp.H (ci.val+1)) (wp.A ci.val) (wp.s_after ci.val) wp.b wp.siteFuel (code .penalty) (wp.values ci))
    (hAp : ∀ t, wp.A 0 t = penaltyA0 sources p den hden k r scratch n x bits hp t) (hHp : ∀ t, wp.H 0 t = (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (wm : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .moment (xH tables semantics buildSource wp) (xA tables semantics buildSource wp) (cost .moment) (width .moment) (code .moment))
    (em : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .moment ci (wm.H ci.val) (wm.H (ci.val+1)) (wm.A ci.val) (wm.s_after ci.val) wm.b wm.siteFuel (code .moment) (wm.values ci))
    (hAm : ∀ t, (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) → wm.A 0 t = xA tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t)) (hHm : ∀ t, wm.H 0 t = xH tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (wc : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .clause (xH tables semantics buildSource wm) (xA tables semantics buildSource wm) (cost .clause) (width .clause) (code .clause))
    (ec : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .clause ci (wc.H ci.val) (wc.H (ci.val+1)) (wc.A ci.val) (wc.s_after ci.val) wc.b wc.siteFuel (code .clause) (wc.values ci))
    (hAc : ∀ t, (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) → wc.A 0 t = xA tables semantics buildSource wm (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t)) (hHc : ∀ t, wc.H 0 t = xH tables semantics buildSource wm (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t)) :
    xA tables semantics buildSource wc (PCJ374c44bb8b7f47d9_.S.ports sources p k r scratch .moment) =
      xA tables semantics buildSource wm (PCJ374c44bb8b7f47d9_.S.ports sources p k r scratch .moment) := by
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have sv : (C10TailVerdict.scratchT .moment).val = 219 := rfl
  have tv : (CloseoutFinalC10RetainedPhaseFold.tailSlots (PCJda54a286946142d3_BranchPhases.offset sources p k r) (ControllerSelectedContinuation.bodyTapes sources p k r scratch) (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r) (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch) (C10TailVerdict.scratchT .moment)).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 343 := by
    rw [tl_val, sv, if_neg (by decide)]
  exact later_passA tables semantics buildSource wc ec hAc _ (cl_passes sources p k r scratch _ (by omega))

theorem j4_head {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den : Nat} {hden : 0 < den} {k r scratch n : Nat} {x : BitInput n} {bits : List Bool}
    {hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}
    {cost width : Phase → Nat} (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder) (wp : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) (code .penalty))
    (ep : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty ci (wp.H ci.val) (wp.H (ci.val+1)) (wp.A ci.val) (wp.s_after ci.val) wp.b wp.siteFuel (code .penalty) (wp.values ci))
    (hAp : ∀ t, wp.A 0 t = penaltyA0 sources p den hden k r scratch n x bits hp t) (hHp : ∀ t, wp.H 0 t = (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (wm : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .moment (xH tables semantics buildSource wp) (xA tables semantics buildSource wp) (cost .moment) (width .moment) (code .moment))
    (em : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .moment ci (wm.H ci.val) (wm.H (ci.val+1)) (wm.A ci.val) (wm.s_after ci.val) wm.b wm.siteFuel (code .moment) (wm.values ci))
    (hAm : ∀ t, (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) → wm.A 0 t = xA tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t)) (hHm : ∀ t, wm.H 0 t = xH tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (wc : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .clause (xH tables semantics buildSource wm) (xA tables semantics buildSource wm) (cost .clause) (width .clause) (code .clause))
    (ec : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .clause ci (wc.H ci.val) (wc.H (ci.val+1)) (wc.A ci.val) (wc.s_after ci.val) wc.b wc.siteFuel (code .clause) (wc.values ci))
    (hAc : ∀ t, (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) → wc.A 0 t = xA tables semantics buildSource wm (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t)) (hHc : ∀ t, wc.H 0 t = xH tables semantics buildSource wm (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t)) (i : Fin 475) :
    xH tables semantics buildSource wc (Tl sources p k r scratch i) = 0 := by
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have tv := tl_val sources p k r scratch i
  have hR := tailSlots_region _ _ (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r)
    (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch) i
  have h2 : 2 ≤ (CloseoutFinalC10RetainedPhaseFold.tailSlots (PCJda54a286946142d3_BranchPhases.offset sources p k r) (ControllerSelectedContinuation.bodyTapes sources p k r scratch) (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r) (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch) i).val := by rw [tv]; split_ifs <;> omega
  have h3 : (CloseoutFinalC10RetainedPhaseFold.tailSlots (PCJda54a286946142d3_BranchPhases.offset sources p k r) (ControllerSelectedContinuation.bodyTapes sources p k r scratch) (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r) (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch) i).val < 278 ∨ PCJda54a286946142d3_BranchPhases.offset sources p k r ≤ (CloseoutFinalC10RetainedPhaseFold.tailSlots (PCJda54a286946142d3_BranchPhases.offset sources p k r) (ControllerSelectedContinuation.bodyTapes sources p k r scratch) (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r) (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch) i).val := by rw [tv]; split_ifs <;> omega
  show xH tables semantics buildSource wc (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (CloseoutFinalC10RetainedPhaseFold.tailSlots (PCJda54a286946142d3_BranchPhases.offset sources p k r) (ControllerSelectedContinuation.bodyTapes sources p k r scratch) (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r) (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch) i)) = 0
  rw [later_heads tables semantics buildSource wc ec hHc _ hR h2, later_heads tables semantics buildSource wm em hHm _ hR h2]
  exact pen_later_heads tables semantics buildSource wp ep hAp hHp _ hR h3

theorem j4_words {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den : Nat} {hden : 0 < den} {k r scratch n : Nat} {x : BitInput n} {bits : List Bool}
    {hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}
    {cost width : Phase → Nat} (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder) (wp : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) (code .penalty))
    (ep : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty ci (wp.H ci.val) (wp.H (ci.val+1)) (wp.A ci.val) (wp.s_after ci.val) wp.b wp.siteFuel (code .penalty) (wp.values ci))
    (hAp : ∀ t, wp.A 0 t = penaltyA0 sources p den hden k r scratch n x bits hp t) (hHp : ∀ t, wp.H 0 t = (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (wm : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .moment (xH tables semantics buildSource wp) (xA tables semantics buildSource wp) (cost .moment) (width .moment) (code .moment))
    (em : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .moment ci (wm.H ci.val) (wm.H (ci.val+1)) (wm.A ci.val) (wm.s_after ci.val) wm.b wm.siteFuel (code .moment) (wm.values ci))
    (hAm : ∀ t, (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) → wm.A 0 t = xA tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t)) (hHm : ∀ t, wm.H 0 t = xH tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (wc : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .clause (xH tables semantics buildSource wm) (xA tables semantics buildSource wm) (cost .clause) (width .clause) (code .clause))
    (ec : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .clause ci (wc.H ci.val) (wc.H (ci.val+1)) (wc.A ci.val) (wc.s_after ci.val) wc.b wc.siteFuel (code .clause) (wc.values ci))
    (hAc : ∀ t, (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) → wc.A 0 t = xA tables semantics buildSource wm (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t)) (hHc : ∀ t, wc.H 0 t = xH tables semantics buildSource wm (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t)) (ph : Phase) (j : Fin 2) :
    xA tables semantics buildSource wc (Tl sources p k r scratch (C10TailSlotsUniform.widthSlotT ph j)) = C10BodyWidths.widthWord (width ph) j := by
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have hj := j.isLt
  have tv := tl_val sources p k r scratch (C10TailSlotsUniform.widthSlotT ph j)
  have wv : (C10TailSlotsUniform.widthSlotT ph j).val = 2 + 2*(C10TailUniformSlots.phaseIndex ph).val + j.val := rfl
  rw [wv] at tv
  have hd := (C10TailUniformSlots.phaseIndex ph).isLt
  have tv' : (CloseoutFinalC10RetainedPhaseFold.tailSlots (PCJda54a286946142d3_BranchPhases.offset sources p k r) (ControllerSelectedContinuation.bodyTapes sources p k r scratch) (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r) (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch) (C10TailSlotsUniform.widthSlotT ph j)).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 126 + 2*(C10TailUniformSlots.phaseIndex ph).val + j.val := by
    rw [tv]; split_ifs <;> omega
  show xA tables semantics buildSource wc (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (CloseoutFinalC10RetainedPhaseFold.tailSlots (PCJda54a286946142d3_BranchPhases.offset sources p k r) (ControllerSelectedContinuation.bodyTapes sources p k r scratch) (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r) (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch) (C10TailSlotsUniform.widthSlotT ph j))) = _
  cases ph with
  | penalty =>
    have d0 : (C10TailUniformSlots.phaseIndex Phase.penalty).val = 0 := rfl
    rw [chainA tables semantics buildSource wp ep hAp hHp wm em hAm hHm wc ec hAc hHc _ (cl_passes sources p k r scratch _ (by omega))
      (mom_passes sources p k r scratch _ (by omega))]
    exact exit_words tables semantics buildSource wp j
  | moment =>
    have d1 : (C10TailUniformSlots.phaseIndex Phase.moment).val = 1 := rfl
    rw [later_passA tables semantics buildSource wc ec hAc _ (cl_passes sources p k r scratch _ (by omega))]
    exact exit_words tables semantics buildSource wm j
  | clause => exact exit_words tables semantics buildSource wc j

theorem j4_blank {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den : Nat} {hden : 0 < den} {k r scratch n : Nat} {x : BitInput n} {bits : List Bool}
    {hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}
    {cost width : Phase → Nat} (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder) (wp : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) (code .penalty))
    (ep : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty ci (wp.H ci.val) (wp.H (ci.val+1)) (wp.A ci.val) (wp.s_after ci.val) wp.b wp.siteFuel (code .penalty) (wp.values ci))
    (hAp : ∀ t, wp.A 0 t = penaltyA0 sources p den hden k r scratch n x bits hp t) (hHp : ∀ t, wp.H 0 t = (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (wm : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .moment (xH tables semantics buildSource wp) (xA tables semantics buildSource wp) (cost .moment) (width .moment) (code .moment))
    (em : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .moment ci (wm.H ci.val) (wm.H (ci.val+1)) (wm.A ci.val) (wm.s_after ci.val) wm.b wm.siteFuel (code .moment) (wm.values ci))
    (hAm : ∀ t, (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) → wm.A 0 t = xA tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t)) (hHm : ∀ t, wm.H 0 t = xH tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (wc : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .clause (xH tables semantics buildSource wm) (xA tables semantics buildSource wm) (cost .clause) (width .clause) (code .clause))
    (ec : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .clause ci (wc.H ci.val) (wc.H (ci.val+1)) (wc.A ci.val) (wc.s_after ci.val) wc.b wc.siteFuel (code .clause) (wc.values ci))
    (hAc : ∀ t, (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) → wc.A 0 t = xA tables semantics buildSource wm (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t)) (hHc : ∀ t, wc.H 0 t = xH tables semantics buildSource wm (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t)) (i : Fin 475) (hi : (15 ≤ i.val ∧ i.val < 102) ∨ 221 ≤ i.val) :
    xA tables semantics buildSource wc (Tl sources p k r scratch i) = [] := by
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have hi' := i.isLt
  have tv := tl_val sources p k r scratch i
  show xA tables semantics buildSource wc (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (CloseoutFinalC10RetainedPhaseFold.tailSlots (PCJda54a286946142d3_BranchPhases.offset sources p k r) (ControllerSelectedContinuation.bodyTapes sources p k r scratch) (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r) (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch) i)) = []
  by_cases h473 : i.val = 473
  · rw [if_pos h473] at tv
    rw [chainA tables semantics buildSource wp ep hAp hHp wm em hAm hHm wc ec hAc hHc _ (passes_217 sources p k r scratch .clause _ tv)
      (passes_217 sources p k r scratch .moment _ tv),
      passA tables semantics buildSource wp ep _ (passes_217 sources p k r scratch .penalty _ tv), hAp,
      penaltyA0_off sources p den hden k r scratch n x bits hp _ (by omega)]
    exact pen_low sources p den hden k r scratch n x bits hp _ (by omega) (by omega) (by omega) (by omega) (by omega)
  · rw [if_neg h473] at tv
    rw [chainA tables semantics buildSource wp ep hAp hHp wm em hAm hHm wc ec hAc hHc _ (cl_passes sources p k r scratch _ (by omega))
      (mom_passes sources p k r scratch _ (by omega))]
    exact pen_blank tables semantics buildSource wp ep hAp hHp _
      (pen_passes .moment (Or.inl rfl) sources p k r scratch _ (by omega)) (by omega) (by omega)

/-! ## 7. The consumer's `SelectedWitness` -/

/-- **`SelectedWitness` from the three phase witnesses** and their start relations. Exits are the realized
exits (J1), runs are `realize.run`; J2/J4 from part 6, J3 and `fits` supplied. -/
def SelectedWitness.ofPhases {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den : Nat} {hden : 0 < den} {k r scratch n : Nat} {x : BitInput n} {bits : List Bool}
    {hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {remainingFuel : Nat} {width : Phase → Nat}
    {code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}
    (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder) (cost : Phase → Nat)
    (wp : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) (code .penalty))
    (ep : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty ci (wp.H ci.val) (wp.H (ci.val+1)) (wp.A ci.val) (wp.s_after ci.val) wp.b wp.siteFuel (code .penalty) (wp.values ci))
    (hAp : ∀ t, wp.A 0 t = penaltyA0 sources p den hden k r scratch n x bits hp t) (hHp : ∀ t, wp.H 0 t = (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (wm : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .moment (xH tables semantics buildSource wp) (xA tables semantics buildSource wp) (cost .moment) (width .moment) (code .moment))
    (em : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .moment ci (wm.H ci.val) (wm.H (ci.val+1)) (wm.A ci.val) (wm.s_after ci.val) wm.b wm.siteFuel (code .moment) (wm.values ci))
    (hAm : ∀ t, (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) → wm.A 0 t = xA tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t)) (hHm : ∀ t, wm.H 0 t = xH tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (wc : PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .clause (xH tables semantics buildSource wm) (xA tables semantics buildSource wm) (cost .clause) (width .clause) (code .clause))
    (ec : ∀ ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)), SourceClauseExit mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .clause ci (wc.H ci.val) (wc.H (ci.val+1)) (wc.A ci.val) (wc.s_after ci.val) wc.b wc.siteFuel (code .clause) (wc.values ci))
    (hAc : ∀ t, (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) → wc.A 0 t = xA tables semantics buildSource wm (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t)) (hHc : ∀ t, wc.H 0 t = xH tables semantics buildSource wm (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t))
    (hthr : ∀ ph, C10ThresholdWidths.thresholdWidth (constantsOf sources) ≤ width ph)
    (fits : PCJ374c44bb8b7f47d9_.branchFuel cost width + 2 ≤ remainingFuel) :
    SelectedWitness mask selector packets rows compiler sources p den hden k r scratch n x bits hp
      site remainingFuel width code where
  cost := cost
  exitH := fun ph => match ph with
    | .penalty => xH tables semantics buildSource wp
    | .moment => xH tables semantics buildSource wm
    | .clause => xH tables semantics buildSource wc
  exitA := fun ph => match ph with
    | .penalty => xA tables semantics buildSource wp
    | .moment => xA tables semantics buildSource wm
    | .clause => xA tables semantics buildSource wc
  penalty := wp
  moment := wm
  clause := wc
  penaltyRun := (maskedBuildPhase mask selector packets rows compiler tables semantics buildSource sources p k den r
    scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) wp.spec).realize.run
  momentRun := (maskedBuildPhase mask selector packets rows compiler tables semantics buildSource sources p k den r
    scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .moment (xH tables semantics buildSource wp) (xA tables semantics buildSource wp) (cost .moment) (width .moment)
    wm.spec).realize.run
  clauseRun := (maskedBuildPhase mask selector packets rows compiler tables semantics buildSource sources p k den r
    scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .clause (xH tables semantics buildSource wm) (xA tables semantics buildSource wm) (cost .clause) (width .clause)
    wc.spec).realize.run
  penaltyKept := j2_pen tables semantics buildSource wp ep hAp hHp wm em hAm hHm wc ec hAc hHc
  momentKept := j2_mom tables semantics buildSource wp ep hAp hHp wm em hAm hHm wc ec hAc hHc
  threshold := hthr
  head := j4_head tables semantics buildSource wp ep hAp hHp wm em hAm hHm wc ec hAc hHc
  words := j4_words tables semantics buildSource wp ep hAp hHp wm em hAm hHm wc ec hAc hHc
  blank := j4_blank tables semantics buildSource wp ep hAp hHp wm em hAm hHm wc ec hAc hHc
  fits := fits

/-- **End to end: `SelectedWitness` from the three clause loops.** The penalty loop starts at `penaltyA0`, the
moment loop at `laterA0` of the penalty exit, the clause loop at `laterA0` of the moment exit (heads unchanged);
every record field (D1-D7), loop field (E1-E7), entry (C2-C4), run (J1), kept record (J2), threshold (J3) and tail
fact (J4) is produced; only the per-clause `ClauseLoop`s, their start equations, the uniformity `hL/hT`, the
per-clause costs and the consumer's fuel/width equations, and `fits` (J5) are inputs. -/
def SelectedWitness.ofLoops {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den : Nat} {hden : 0 < den} {k r scratch n : Nat} {x : BitInput n} {bits : List Bool}
    {hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {remainingFuel : Nat} {width : Phase → Nat}
    {code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}
    (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder) (cost : Phase → Nat)
    (S : CloseoutFinalC10ModeNativeSchedule.Selection sources p k) (hn : S.onset ≤ n) (hr : r = S.exponent)
    -- the penalty loop
    (Lp : ClauseLoop mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site
      (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty (C10PartsSchedule.entryWidthSchedule sources k r n) (code .penalty))
    (hA0p : Lp.A 0 = penaltyA0 sources p den hden k r scratch n x bits hp)
    (hH0p : Lp.H 0 = fun j => (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j))
    (lsp : Nat) (hLp : ∀ c, (Lp.values c).L = lsp) (hTp : ∀ c, (Lp.values c).target = (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)))
    (cp : Nat)
    (hcp : 4*NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)+PCPPQueryCachedBounds.callBudget (CloseoutLanguage.selectedPCPP sources)
      ((req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).circuit.size+(req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity)+Lp.siteFuel+21 ≤ cp)
    (hfp : cost .penalty = (4*(C10PartsSchedule.entryWidthSchedule sources k r n)+23)+1+(NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)*(cp+3)+3+1+
      CloseoutFinalC10RetainedPhaseFold.fuel (C10PartsSchedule.entryWidthSchedule sources k r n) Lp.entries.length))
    (hwp : width .penalty = CloseoutFinalC10WorkerFold.foldWidth (CompetitorRationalDecision.width (C10PartsSchedule.entryWidthSchedule sources k r n)) Lp.entries)
    -- the moment loop, at the penalty exit
    (Lm : ClauseLoop mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site
      (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .moment (C10PartsSchedule.entryWidthSchedule sources k r n) (code .moment))
    (hA0m : Lm.A 0 = laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp)
      (xA tables semantics buildSource (penaltyW S hn hr Lp hA0p hH0p lsp hLp hTp cp hcp hfp hwp)))
    (hH0m : Lm.H 0 = fun i => xH tables semantics buildSource (penaltyW S hn hr Lp hA0p hH0p lsp hLp hTp cp hcp hfp hwp)
      (PCJda54a286946142d3_BranchPhases.body sources p k r scratch i))
    (lsm : Nat) (hLm : ∀ c, (Lm.values c).L = lsm) (hTm : ∀ c, (Lm.values c).target = (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)))
    (cm : Nat)
    (hcm : 4*NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)+PCPPQueryCachedBounds.callBudget (CloseoutLanguage.selectedPCPP sources)
      ((req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).circuit.size+(req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity)+Lm.siteFuel+21 ≤ cm)
    (hfm : cost .moment = (2*capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)+4)+1+(NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)*(cm+3)+3+1+
      CloseoutFinalC10RetainedPhaseFold.fuel (C10PartsSchedule.entryWidthSchedule sources k r n) Lm.entries.length))
    (hwm : width .moment = CloseoutFinalC10WorkerFold.foldWidth (CompetitorRationalDecision.width (C10PartsSchedule.entryWidthSchedule sources k r n)) Lm.entries)
    -- the clause loop, at the moment exit
    (Lc : ClauseLoop mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site
      (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .clause (C10PartsSchedule.entryWidthSchedule sources k r n) (code .clause))
    (hA0c : Lc.A 0 = laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp)
      (xA tables semantics buildSource (laterW (Or.inl rfl) S hn hr
        (penalty_bank sources p den hden k r scratch n x bits hp).1
        (pen_later tables semantics buildSource (penaltyW S hn hr Lp hA0p hH0p lsp hLp hTp cp hcp hfp hwp) Lp.exits
          (fun t => congrFun hA0p t) (fun t => congrFun hH0p t) .moment (Or.inl rfl))
        Lm hA0m hH0m lsm hLm hTm cm hcm hfm hwm)))
    (hH0c : Lc.H 0 = fun i => xH tables semantics buildSource (laterW (Or.inl rfl) S hn hr
        (penalty_bank sources p den hden k r scratch n x bits hp).1
        (pen_later tables semantics buildSource (penaltyW S hn hr Lp hA0p hH0p lsp hLp hTp cp hcp hfp hwp) Lp.exits
          (fun t => congrFun hA0p t) (fun t => congrFun hH0p t) .moment (Or.inl rfl))
        Lm hA0m hH0m lsm hLm hTm cm hcm hfm hwm) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch i))
    (lsc : Nat) (hLc : ∀ c, (Lc.values c).L = lsc) (hTc : ∀ c, (Lc.values c).target = (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)))
    (cc : Nat)
    (hcc : 4*NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)+PCPPQueryCachedBounds.callBudget (CloseoutLanguage.selectedPCPP sources)
      ((req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).circuit.size+(req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity)+Lc.siteFuel+21 ≤ cc)
    (hfc : cost .clause = (2*capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)+4)+1+(NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)*(cc+3)+3+1+
      CloseoutFinalC10RetainedPhaseFold.fuel (C10PartsSchedule.entryWidthSchedule sources k r n) Lc.entries.length))
    (hwc : width .clause = CloseoutFinalC10WorkerFold.foldWidth (CompetitorRationalDecision.width (C10PartsSchedule.entryWidthSchedule sources k r n)) Lc.entries)
    (fits : PCJ374c44bb8b7f47d9_.branchFuel cost width + 2 ≤ remainingFuel) :
    SelectedWitness mask selector packets rows compiler sources p den hden k r scratch n x bits hp
      site remainingFuel width code :=
  let wp := penaltyW S hn hr Lp hA0p hH0p lsp hLp hTp cp hcp hfp hwp
  have hm := (penalty_bank sources p den hden k r scratch n x bits hp).1
  have hAp : ∀ t, wp.A 0 t = penaltyA0 sources p den hden k r scratch n x bits hp t := fun t => congrFun hA0p t
  have hHp : ∀ t, wp.H 0 t = (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) := fun t => congrFun hH0p t
  let wm := laterW (Or.inl rfl) S hn hr hm (pen_later tables semantics buildSource wp Lp.exits hAp hHp .moment (Or.inl rfl))
    Lm hA0m hH0m lsm hLm hTm cm hcm hfm hwm
  have hAm : ∀ t, (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) → wm.A 0 t = xA tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) :=
    fun t ht => (congrFun hA0m t).trans (laterA0_off sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) _ t ht)
  have hHm : ∀ t, wm.H 0 t = xH tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) := fun t => congrFun hH0m t
  let wc := laterW (Or.inr rfl) S hn hr hm
    (later_pass tables semantics buildSource wm Lm.exits hAm hHm
      (pen_later tables semantics buildSource wp Lp.exits hAp hHp .clause (Or.inr rfl)))
    Lc hA0c hH0c lsc hLc hTc cc hcc hfc hwc
  have hAc : ∀ t, (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) → wc.A 0 t = xA tables semantics buildSource wm (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) :=
    fun t ht => (congrFun hA0c t).trans (laterA0_off sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) _ t ht)
  have hHc : ∀ t, wc.H 0 t = xH tables semantics buildSource wm (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) := fun t => congrFun hH0c t
  have hthr : ∀ ph, C10ThresholdWidths.thresholdWidth (constantsOf sources) ≤ width ph := by
    intro ph
    cases ph with
    | penalty => rw [hwp]; exact phase_threshold sources k r n _
    | moment => rw [hwm]; exact phase_threshold sources k r n _
    | clause => rw [hwc]; exact phase_threshold sources k r n _
  SelectedWitness.ofPhases tables semantics buildSource cost wp Lp.exits hAp hHp wm Lm.exits hAm hHm
    wc Lc.exits hAc hHc hthr fits

end
end NearCubicWires.SourcePhase
end

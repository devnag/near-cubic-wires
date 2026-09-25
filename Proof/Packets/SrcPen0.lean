import Proof.Packets.SrcPen0Bank
import Proof.SourceAssembly.SourceStepsStartHole

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction NearCubicWires.SourceSkeleton
namespace NearCubicWires.SourceStart.Pen0
open NearCubicWires.SourceSteps
noncomputable section
attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size

section pen
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
  (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
  (hp : P1Independent.CappedLegalAdmission.passed sources p
    (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
    (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)

/-- The body cache sits on `{0, 1} ∪ [P, offset)`, never on tape `1`. -/
theorem cache_vals (mode : Bool) (i : Fin 19) :
    ((PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i).val = 0 ∨
      (WorkspaceSelectedEntry.size sources k r p.clauseDegree ≤ (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i).val ∧
       (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i).val < PCJda54a286946142d3_BranchPhases.offset sources p k r)) := by
  have hc := (WorkspaceSelectedEntryReady.cache sources p k mode i).isLt
  have h1 := ready_cache_ne_one sources p k mode i
  have hP := size_302 sources p k r
  have hoff : PCJda54a286946142d3_BranchPhases.offset sources p k r =
      WorkspaceSelectedEntry.size sources k r p.clauseDegree + WorkspaceSelectedAdmission.originalTapes sources p k - 2 := rfl
  have e : (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i).val =
      if (WorkspaceSelectedEntryReady.cache sources p k mode i).val < 2 then (WorkspaceSelectedEntryReady.cache sources p k mode i).val
      else WorkspaceSelectedEntry.size sources k r p.clauseDegree + (WorkspaceSelectedEntryReady.cache sources p k mode i).val - 2 := rfl
  rw [e]
  split_ifs with h
  · left; omega
  · right; constructor <;> omega

/-- A tape off the cache's value set is not a cache tape. -/
theorem not_cache (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch))
    (ht : (2 ≤ t.val ∧ t.val < WorkspaceSelectedEntry.size sources k r p.clauseDegree) ∨ PCJda54a286946142d3_BranchPhases.offset sources p k r ≤ t.val) (i : Fin 19) :
    t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i := by
  intro he
  have hv := cache_vals sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i
  rw [← he] at hv
  have hP := size_302 sources p k r
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  omega

/-- The penalty bank is blank from `offset + 96` on, off the first-entry slots. -/
theorem blank_off (j : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (hj : PCJda54a286946142d3_BranchPhases.offset sources p k r + 96 ≤ j.val) (hf : ∀ i, (fSlots sources p k r scratch i).val ≠ j.val) :
    penaltyA0 sources p den hden k r scratch n x bits hp j = [] := by
  have pb := penalty_bank sources p den hden k r scratch n x bits hp
  dsimp only at pb
  obtain ⟨_, _, _, _, _, hfar, _, _, _, _⟩ := pb
  unfold penaltyA0
  rw [install_other _ _ _ _ (fun i he => hf i (congrArg Fin.val he))]
  exact hfar j hj

theorem fs_bound (i : Fin 10) : (fSlots sources p k r scratch i).val = 218 ∨
    (PCJda54a286946142d3_BranchPhases.offset sources p k r + 124 ≤ (fSlots sources p k r scratch i).val ∧ (fSlots sources p k r scratch i).val ≤ PCJda54a286946142d3_BranchPhases.offset sources p k r + 1095) := by
  fin_cases i <;> simp [fSlots, CloseoutFinalC10FirstPhaseEntry.firstSlots]

theorem fs_ne (i : Fin 10) : (fSlots sources p k r scratch i).val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 680 ∧
    (fSlots sources p k r scratch i).val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 958 := by
  fin_cases i <;> simp [fSlots, CloseoutFinalC10FirstPhaseEntry.firstSlots]

/-- The penalty bank is blank from `offset + 1155` on. -/
theorem blank_far (j : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (hj : PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 ≤ j.val) : penaltyA0 sources p den hden k r scratch n x bits hp j = [] := by
  refine blank_off sources p den hden k r scratch n x bits hp j (by omega) (fun i he => ?_)
  have := fs_bound sources p k r scratch i
  omega

include hp in
/-- Heads are `0` off the prologue's last port. -/
theorem head_zero (j : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (hj : j.val ≠ WorkspaceSelectedEntry.size sources k r p.clauseDegree - 1) : PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j) = 0 := by
  have pb := penalty_bank sources p den hden k r scratch n x bits hp
  dsimp only at pb
  exact pb.2.2.2.2.2.2.2.2.1 j hj

/-- The queried penalty bank and its heads at any tape past `offset + 1155`. -/
theorem far_pair (j : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (hj : PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 ≤ j.val) :
    queriedAt sources p den hden k r scratch n x bits hp 0 (penaltyA0 sources p den hden k r scratch n x bits hp) j = [] ∧ PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j) = 0 := by
  have hP := size_302 sources p k r
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have hoff : PCJda54a286946142d3_BranchPhases.offset sources p k r = WorkspaceSelectedEntry.size sources k r p.clauseDegree + WorkspaceSelectedAdmission.originalTapes sources p k - 2 := rfl
  have ht := WorkspaceSelectedEntryReady.old_size sources p k
  rw [queriedAt_off sources p den hden k r scratch n x bits hp 0 _ _ (not_cache sources p den hden k r scratch n x bits hp j (Or.inr (by omega)))]
  exact ⟨blank_far sources p den hden k r scratch n x bits hp j hj, head_zero sources p den hden k r scratch n x bits hp j (by omega)⟩

structure Pen0Facts (E : EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) : Prop where
  hwhole : ∀ i, (E.whole i).val = i.val
  hFo : PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 ≤ E.d.F
  hcnt : E.d.F ≤ E.cnt.val
  har : E.whole (E.pl .penalty).ar = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) 13
  hq : E.q = (req sources k (PolynomialClock.ordinaryClock k) x
    (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity
  hwd : E.whole (E.pl .penalty).wd = Wd sources p k r scratch .penalty 218
  hb : E.b = C10PartsSchedule.entryWidthSchedule sources k r n
  hCe : P1TopDown.WorkspaceSelectedEntryBudget.envelope sources p k r n + 1 ≤ E.Ce
  h15 : E.whole E.c15 = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) 15
  h17 : E.whole E.c17 = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) 17
  h18 : E.whole E.c18 = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) 18
  h284 : E.q284.val = 284
  hKpen : ∀ y, E.Kc y → y.val < E.d.F → (y.val < 278 ∨ 285 ≤ y.val) → E.KH0 y = 0 ∧
    ((∃ i, E.whole y = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i ∧ E.K0 .penalty 0 y = cdAt sources p k n x bits 0 i) ∨
     (y.val = 1 ∧ E.K0 .penalty 0 y = RepairOrdinary.frame bits) ∨
     (E.whole y = PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch ∧
        E.K0 .penalty 0 y = List.replicate (NC sources k (PolynomialClock.ordinaryClock k) x
          (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) true))

/-- `pen0`'s query facts (`QueryAt0` at clause `0`). -/
theorem pen0_query (E : EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (h : Pen0Facts sources p den hden k r scratch n x bits hp E) :
    QueryAt0 E.c15 E.q284 E.c17 E.c18 (capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) (ZeroPadding.pad (capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) (qwordAt sources p k n x bits 0)) (fun i => PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (E.whole i))) (fun i => queriedAt sources p den hden k r scratch n x bits hp 0 (penaltyA0 sources p den hden k r scratch n x bits hp) (E.whole i)) := by
  have hP := size_302 sources p k r
  have ps := penalty_start sources p den hden k r scratch n x bits hp
  dsimp only at ps
  obtain ⟨_, _, _, _, _, _, _, pcH, _⟩ := ps
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show queriedAt sources p den hden k r scratch n x bits hp 0 _ (E.whole E.c15) = _
    rw [h.h15, queriedAt_cache, cdAt_15]
  · show queriedAt sources p den hden k r scratch n x bits hp 0 _ (E.whole E.c17) = _
    rw [h.h17, queriedAt_cache, cdAt_17]
  · show queriedAt sources p den hden k r scratch n x bits hp 0 _ (E.whole E.c18) = _
    rw [h.h18, queriedAt_cache, cdAt_18]
  · show PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (E.whole E.c15)) = 0
    rw [h.h15]; exact pcH 15
  · show PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (E.whole E.q284)) = 0
    exact head_zero sources p den hden k r scratch n x bits hp _ (by rw [h.hwhole, h.h284]; omega)
  · show PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (E.whole E.c17)) = 0
    rw [h.h17]; exact pcH 17
  · show PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (E.whole E.c18)) = 0
    rw [h.h18]; exact pcH 18

/-- `pen0`'s first-entry facts (`FirstEntry4`). -/
theorem pen0_first (E : EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (h : Pen0Facts sources p den hden k r scratch n x bits hp E) :
    FirstEntry4 (E.pl .penalty) E.q E.b E.Rc E.Ce E.Kc (E.K0 .penalty 0) E.KH0 E.cnt (fun i => PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (E.whole i))) (fun i => queriedAt sources p den hden k r scratch n x bits hp 0 (penaltyA0 sources p den hden k r scratch n x bits hp) (E.whole i)) := by
  have hP := size_302 sources p k r
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have hoff : PCJda54a286946142d3_BranchPhases.offset sources p k r = WorkspaceSelectedEntry.size sources k r p.clauseDegree + WorkspaceSelectedAdmission.originalTapes sources p k - 2 := rfl
  have ht := WorkspaceSelectedEntryReady.old_size sources p k
  have ps := penalty_start sources p den hden k r scratch n x bits hp
  dsimp only at ps
  obtain ⟨_p1, _p2, _p3, _p4, p218, _p81, _p90, pcH, ptH, ptA, _pcA, pWH, _⟩ := ps
  have farY : ∀ y : Fin E.T, E.d.F ≤ y.val →
      queriedAt sources p den hden k r scratch n x bits hp 0 (penaltyA0 sources p den hden k r scratch n x bits hp) (E.whole y) = [] ∧
      PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (E.whole y)) = 0 := by
    intro y hy
    have hv := h.hwhole y
    have hF := h.hFo
    exact far_pair sources p den hden k r scratch n x bits hp (E.whole y) (by omega)
  have hscrF : E.d.F ≤ (E.d.scr (E.pl .penalty).hT 11).val := by
    show E.d.F ≤ E.d.scrV 11
    unfold SourceConstruction.Dims.scrV SourceConstruction.Dims.G; omega
  refine ⟨(farY _ hscrF).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show queriedAt sources p den hden k r scratch n x bits hp 0 _ (E.whole (E.pl .penalty).ar) = _
    rw [h.har, queriedAt_cache, h.hq]
    simp [cdAt, PCPPQueryIndexPadding.clauseData, PCPPQueryClauseReuse.data]
  · show PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (E.whole (E.pl .penalty).ar)) = 0
    rw [h.har]; exact pcH 13
  · show queriedAt sources p den hden k r scratch n x bits hp 0 _ (E.whole (E.pl .penalty).wd) = _
    have hw218 : (Wd sources p k r scratch .penalty 218).val = 218 := by
      have d0 : (C10TailUniformSlots.phaseIndex Phase.penalty).val = 0 := rfl
      have e218 : (218 : Fin 278).val = 218 := rfl
      rcases wd_cases sources p k r scratch .penalty 218 with hc | hc | hc | hc
      · omega
      · omega
      · omega
      · omega
    rw [h.hwd, queriedAt_off sources p den hden k r scratch n x bits hp 0 _ _
      (not_cache sources p den hden k r scratch n x bits hp _ (Or.inl (by omega))), p218, h.hb]
  · show PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (E.whole (E.pl .penalty).wd)) = 0
    rw [h.hwd]; exact pWH 218
  · intro y h1 h2
    have hv := h.hwhole y
    show (queriedAt sources p den hden k r scratch n x bits hp 0 _ (E.whole y)).length ≤ E.Ce ∧
      PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (E.whole y)) = 0
    rw [queriedAt_off sources p den hden k r scratch n x bits hp 0 _ _
      (not_cache sources p den hden k r scratch n x bits hp _ (Or.inl (by omega)))]
    obtain ⟨hl, hh⟩ := penalty_residue5 sources p den hden k r scratch n x bits hp (E.whole y) (by omega) (by omega)
    exact ⟨hl.trans h.hCe, hh⟩
  · intro y h1 _
    exact farY y h1
  · intro y hK hF hr
    obtain ⟨hKH, hc⟩ := h.hKpen y hK hF hr
    show queriedAt sources p den hden k r scratch n x bits hp 0 _ (E.whole y) = E.K0 .penalty 0 y ∧
      PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (E.whole y)) = E.KH0 y
    rw [hKH]
    rcases hc with ⟨i, hwi, hk0⟩ | ⟨hy1, hk0⟩ | ⟨hwt, hk0⟩
    · rw [hwi, queriedAt_cache, hk0]
      exact ⟨rfl, pcH i⟩
    · have hv := h.hwhole y
      have hne : ∀ i, E.whole y ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i := by
        intro i he
        have hc := cache_vals sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i
        rw [← he] at hc
        omega
      rw [queriedAt_off sources p den hden k r scratch n x bits hp 0 _ _ hne, hk0]
      exact penalty_1 sources p den hden k r scratch n x bits hp (E.whole y) (by omega)
    · have htv : (PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 53 := rfl
      rw [hwt, queriedAt_off sources p den hden k r scratch n x bits hp 0 _ _
        (not_cache sources p den hden k r scratch n x bits hp _ (Or.inr (by omega))), ptA, hk0]
      exact ⟨rfl, ptH⟩
  · show (queriedAt sources p den hden k r scratch n x bits hp 0 _ (E.whole E.cnt)).length ≤ E.Rc
    rw [(farY E.cnt h.hcnt).1]
    exact Nat.zero_le _
  · show PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (E.whole E.cnt)) ≤ E.Rc
    rw [(farY E.cnt h.hcnt).2]
    exact Nat.zero_le _

/-- A later phase's word slot `81` is blank at the penalty entry (head `0`). -/
theorem later81 (ph : Phase) (hph : ph = Phase.moment ∨ ph = Phase.clause) :
    penaltyA0 sources p den hden k r scratch n x bits hp (Wd sources p k r scratch ph 81) = [] ∧
    PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Wd sources p k r scratch ph 81)) = 0 := by
  have hP := size_302 sources p k r
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have hoff : PCJda54a286946142d3_BranchPhases.offset sources p k r = WorkspaceSelectedEntry.size sources k r p.clauseDegree + WorkspaceSelectedAdmission.originalTapes sources p k - 2 := rfl
  have e81v : (81 : Fin 278).val = 81 := rfl
  have hv : (Wd sources p k r scratch ph 81).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 680 ∨ (Wd sources p k r scratch ph 81).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 958 := by
    rcases hph with rfl | rfl
    · have d1 : (C10TailUniformSlots.phaseIndex Phase.moment).val = 1 := rfl
      rcases wd_cases sources p k r scratch .moment 81 with hc | hc | hc | hc
      · omega
      · omega
      · omega
      · left; omega
    · have d2 : (C10TailUniformSlots.phaseIndex Phase.clause).val = 2 := rfl
      rcases wd_cases sources p k r scratch .clause 81 with hc | hc | hc | hc
      · omega
      · omega
      · omega
      · right; omega
  refine ⟨blank_off sources p den hden k r scratch n x bits hp _ (by omega) (fun i he => ?_),
    head_zero sources p den hden k r scratch n x bits hp _ (by omega)⟩
  have hne := fs_ne sources p k r scratch i
  rcases hv with hc | hc
  · exact hne.1 (he.trans hc)
  · exact hne.2 (he.trans hc)

/-- A later phase's word slot `90` holds `word 0` at the penalty entry (head `0`). -/
theorem later90 (ph : Phase) (hph : ph = Phase.moment ∨ ph = Phase.clause) :
    penaltyA0 sources p den hden k r scratch n x bits hp (Wd sources p k r scratch ph 90) = CompareMachine.word 0 ∧
    PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Wd sources p k r scratch ph 90)) = 0 := by
  have hP := size_302 sources p k r
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have hoff : PCJda54a286946142d3_BranchPhases.offset sources p k r = WorkspaceSelectedEntry.size sources k r p.clauseDegree + WorkspaceSelectedAdmission.originalTapes sources p k - 2 := rfl
  have spec := firstLocal_spec (C10PartsSchedule.entryWidthSchedule sources k r n)
  obtain ⟨_w2, _w4, w6, w8⟩ := wd_fslot sources p k r scratch
  have e90v : (90 : Fin 278).val = 90 := rfl
  have hv : (Wd sources p k r scratch ph 90).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 689 ∨ (Wd sources p k r scratch ph 90).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 967 := by
    rcases hph with rfl | rfl
    · have d1 : (C10TailUniformSlots.phaseIndex Phase.moment).val = 1 := rfl
      rcases wd_cases sources p k r scratch .moment 90 with hc | hc | hc | hc
      · omega
      · omega
      · omega
      · left; omega
    · have d2 : (C10TailUniformSlots.phaseIndex Phase.clause).val = 2 := rfl
      rcases wd_cases sources p k r scratch .clause 90 with hc | hc | hc | hc
      · omega
      · omega
      · omega
      · right; omega
  refine ⟨?_, head_zero sources p den hden k r scratch n x bits hp _ (by omega)⟩
  rcases hph with rfl | rfl
  · rw [w6]
    unfold penaltyA0
    rw [install_slot _ (CloseoutFinalC10FirstPhaseEntry.slots_injective _ _ _ _)]
    exact spec.2.2.2.2.2.1
  · rw [w8]
    unfold penaltyA0
    rw [install_slot _ (CloseoutFinalC10FirstPhaseEntry.slots_injective _ _ _ _)]
    exact spec.2.2.2.2.2.2

/-- `pen0`'s phase words at `(penalty, 0)`. -/
theorem pen0_words (b : Nat)
    (EF : Phase → Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) →
      List CloseoutRowsEstimatorCoefficients.Stream.Entry) :
    PhaseWords sources p k r scratch n x bits b EF .penalty 0 (penaltyA0 sources p den hden k r scratch n x bits hp)
      (fun j => PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j)) := by
  have ps := penalty_start sources p den hden k r scratch n x bits hp
  dsimp only at ps
  obtain ⟨_p1, _p2, _p3, _p4, _p218, p81, p90, _pcH, _ptH, _ptA, _pcA, pWH, _⟩ := ps
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show penaltyA0 sources p den hden k r scratch n x bits hp (Wd sources p k r scratch .penalty 81) = CloseoutRowsEstimatorCoefficients.Stream.words b (prefixEntries (EF .penalty) 0)
    rw [p81, prefixEntries_zero]; rfl
  · show penaltyA0 sources p den hden k r scratch n x bits hp (Wd sources p k r scratch .penalty 90) = CompareMachine.word (prefixEntries (EF .penalty) 0).length
    rw [p90, prefixEntries_zero]; rfl
  · exact pWH 81
  · exact pWH 90
  · intro ph' hLp
    have hph : ph' = Phase.moment ∨ ph' = Phase.clause := by
      rcases hLp with ⟨_, hh⟩ | ⟨hh, _⟩
      · exact hh
      · cases hh
    obtain ⟨a81, h81⟩ := later81 sources p den hden k r scratch n x bits hp ph' hph
    obtain ⟨a90, h90⟩ := later90 sources p den hden k r scratch n x bits hp ph' hph
    exact ⟨a81, a90, h81, h90⟩

theorem pen0_generic (E : EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r scratch))
    (EF : Phase → Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) →
      List CloseoutRowsEstimatorCoefficients.Stream.Entry)
    (h : Pen0Facts sources p den hden k r scratch n x bits hp E) :
    Pen0Hole sources p den hden k r scratch n x bits hp E EF :=
  ⟨entryInvAt2_first sources p den hden k r scratch n x bits hp E _ _
      (pen0_query sources p den hden k r scratch n x bits hp E h) (pen0_first sources p den hden k r scratch n x bits hp E h),
    pen0_words sources p den hden k r scratch n x bits hp E.b EF, fun hc => absurd ⟨rfl, rfl⟩ hc⟩

end pen

end
end NearCubicWires.SourceStart.Pen0


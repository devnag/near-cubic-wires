import Proof.SourceAssembly.SourceStepsEntryInv2

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 400000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction NearCubicWires.SourceSkeleton
namespace NearCubicWires.SourceSteps
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

section inv3
open NearCubicWires.SourceConstruction.InitRun

variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (den : Nat) (hden : 0 < den) (k r scratch n : Nat)
  (x : BitInput n) (bits : List Bool)
  (hp : P1Independent.CappedLegalAdmission.passed sources p
    (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
    (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)

/-- `ph'` runs after `ph`. -/
def LaterPhase (ph ph' : Phase) : Prop :=
  (ph = .penalty ∧ (ph' = .moment ∨ ph' = .clause)) ∨ (ph = .moment ∧ ph' = .clause)

/-- **The emitter/appender words on the site's `encT` tapes** (SI `InitOutM`'s form), all heads `0`, and the carried payload on `encT 5`. -/
def EncWords {d : SourceConstruction.Dims} {T : Nat} (hT : d.U ≤ T) (Rc b : Nat) (H : Fin T → ℕ) (A : Fin T → List Bool) : Prop :=
  (∀ kk : Fin 13, H (Dims.encT (d := d) hT kk) = 0) ∧
  (∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (old : List Bool),
    A (Dims.encT (d := d) hT 3) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 3) ∧
    A (Dims.encT (d := d) hT 6) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 7) ∧
    A (Dims.encT (d := d) hT 7) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 8) ∧
    A (Dims.encT (d := d) hT 8) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 9) ∧
    A (Dims.encT (d := d) hT 9) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 10)) ∧
  (∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (xs : List CloseoutRowsEstimatorCoefficients.Stream.Entry),
    A (Dims.encT (d := d) hT 10) = ZeroPadding.pad Rc (CloseoutFinalC10AppendPositioning.tapes b (D0 b)
      (CloseoutFinalC10AppendWorkspaceInit.capacity b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) en xs 2) ∧
    A (Dims.encT (d := d) hT 11) = ZeroPadding.pad Rc (CloseoutFinalC10AppendPositioning.tapes b (D0 b)
      (CloseoutFinalC10AppendWorkspaceInit.capacity b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) en xs 4) ∧
    A (Dims.encT (d := d) hT 12) = ZeroPadding.pad Rc (CloseoutFinalC10AppendPositioning.tapes b (D0 b)
      (CloseoutFinalC10AppendWorkspaceInit.capacity b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) en xs 5)) ∧
  (∃ w : List Bool, w.length ≤ D0 b ∧ A (Dims.encT (d := d) hT 5) = ZeroPadding.pad Rc w)

/-- **The phase words**: the current phase's append stream / count at the clause's prefix, and every later phase's still blank / `word 0`;
heads `0`. On the body bank. -/
def PhaseWords (b : Nat) (EF : Phase → Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) → List CloseoutRowsEstimatorCoefficients.Stream.Entry)
    (ph : Phase) (ci : Nat) (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (H : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) : Prop :=
  A (Wd sources p k r scratch ph 81) = CloseoutRowsEstimatorCoefficients.Stream.words b (prefixEntries (EF ph) ci) ∧
  A (Wd sources p k r scratch ph 90) = CompareMachine.word (prefixEntries (EF ph) ci).length ∧
  H (Wd sources p k r scratch ph 81) = 0 ∧ H (Wd sources p k r scratch ph 90) = 0 ∧
  (∀ ph' : Phase, LaterPhase ph ph' →
    A (Wd sources p k r scratch ph' 81) = [] ∧ A (Wd sources p k r scratch ph' 90) = CompareMachine.word 0 ∧ H (Wd sources p k r scratch ph' 81) = 0 ∧ H (Wd sources p k r scratch ph' 90) = 0)

open Classical in
/-- **THE CLAUSE-ENTRY INVARIANT, v3** (`StepsContract2.Inv`). -/
def entryInvAt3 (E : EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (EF : Phase → Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) → List CloseoutRowsEstimatorCoefficients.Stream.Entry)
    (ph : Phase) (ci : Nat) (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (H : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) : Prop :=
  entryInvAt2 sources p den hden k r scratch n x bits hp E ph ci A H ∧
  PhaseWords sources p k r scratch n x bits E.b EF ph ci A H ∧
  (¬ (ph = .penalty ∧ ci = 0) → EncWords (E.pl ph).hT E.Rc E.b (fun i => H (E.whole i))
    (fun i => queriedAt sources p den hden k r scratch n x bits hp ci A (E.whole i)))

end inv3

section bridge3
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (den : Nat) (hden : 0 < den) (k r scratch n : Nat)
  (x : BitInput n) (bits : List Bool)
  (hp : P1Independent.CappedLegalAdmission.passed sources p
    (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
    (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)

/-- A later phase's word slots `81`/`90` are kept by the current phase's fold. -/
theorem keeps_later (ph ph' : Phase) (hL : LaterPhase ph ph') (i : Fin 278) (hi : i.val = 81 ∨ i.val = 90) :
    FoldKeeps sources p k r scratch ph (Wd sources p k r scratch ph' i) := by
  have hpi : (C10TailUniformSlots.phaseIndex ph).val = 0 ∧ (C10TailUniformSlots.phaseIndex ph').val ≠ 0 ∨
      (C10TailUniformSlots.phaseIndex ph).val = 1 ∧ (C10TailUniformSlots.phaseIndex ph').val = 2 := by
    rcases hL with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
    · left; exact ⟨rfl, by decide⟩
    · left; exact ⟨rfl, by decide⟩
    · right; exact ⟨rfl, rfl⟩
  have hw := wd_cases sources p k r scratch ph' i
  have hi' := (C10TailUniformSlots.phaseIndex ph').isLt
  have hv : (Wd sources p k r scratch ph' i).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 599 + ((C10TailUniformSlots.phaseIndex ph').val - 1) * 278 + i.val := by
    rcases hw with h | h | h | h
    · omega
    · omega
    · omega
    · exact h.1
  generalize hpa : (C10TailUniformSlots.phaseIndex ph).val = pa at hpi
  generalize hpb : (C10TailUniformSlots.phaseIndex ph').val = pb at hpi hi' hv
  generalize ho : PCJda54a286946142d3_BranchPhases.offset sources p k r = o at hv
  apply keeps_of sources p k r scratch ph _
  all_goals (try simp only [hpa, ho]) ; (try omega)

open Classical in
/-- **THE BRIDGE on `entryInvAt3`** (`StepsContract2.bridge`'s exact type at `Inv := entryInvAt3 … E EF`), from the site-layout facts of `E`. -/
theorem bridge_entryInvAt3 (E : EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r scratch))
    (EF : Phase → Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) → List CloseoutRowsEstimatorCoefficients.Stream.Entry)
    (hwhole : ∀ i, (E.whole i).val = i.val)
    (hFo : PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 ≤ E.d.F)
    (hcnt : E.d.F ≤ E.cnt.val)
    (hKlow : ∀ y, E.Kc y → y.val < E.d.F →
      (∃ i, E.whole y = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) ∨ y.val < 2 ∨ (278 ≤ y.val ∧ y.val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 124))
    (hK0 : ∀ ph ph' : Phase, (ph = .penalty ∧ ph' = .moment) ∨ (ph = .moment ∧ ph' = .clause) →
      ∀ y, E.Kc y → (∀ i, E.whole y ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) → E.K0 ph' 0 y = E.K0 ph (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) y)
    (hK0c : ∀ (ph : Phase) (ci : Nat) y i, E.Kc y → E.whole y = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i → E.K0 ph ci y = cdAt sources p k n x bits ci i)
    (h15 : E.whole E.c15 = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) 15) (h17 : E.whole E.c17 = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) 17)
    (h18 : E.whole E.c18 = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) 18) (h284 : E.q284.val = 284) :
    ∀ (ph ph' : Phase), (ph = .penalty ∧ ph' = .moment) ∨ (ph = .moment ∧ ph' = .clause) →
    ∀ (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (H : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
      (A' : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool) (H' : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → Nat),
      entryInvAt3 sources p den hden k r scratch n x bits hp E EF ph (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) A H →
      (∀ t, (∀ j, Wd sources p k r scratch ph j ≠ t) → (∀ j, Fd sources p k r scratch ph j ≠ t) →
        A' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = A t) →
      (∀ t, H' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = H t) →
      (∀ i : Fin 218, (i = 0 ∨ i = 1 ∨ i = 216 ∨ i = 217) →
        A' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Fd sources p k r scratch ph (i.castAdd 1))) =
          A (Fd sources p k r scratch ph (i.castAdd 1))) →
      entryInvAt3 sources p den hden k r scratch n x bits hp E EF ph' 0 (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A')
        (fun i => H' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch i)) := by
  intro ph ph' hph A H A' H' hInv hframe hheads hprot
  obtain ⟨hI2, hPW, hEW⟩ := hInv
  have hNC := nc_pos sources p k n x bits
  have hphNC : ¬ (ph = .penalty ∧ NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) = 0) := fun h => absurd h.2 (Nat.pos_iff_ne_zero.mp hNC)
  have hph' : ¬ (ph' = .penalty ∧ (0 : Nat) = 0) := by
    rcases hph with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
  have hkeepA := keep_exit sources p k r scratch ph A A' hframe hprot
  have hoff := offset_ge_300 sources p k r
  have hLph : LaterPhase ph ph' := by
    rcases hph with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, Or.inl rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  refine ⟨bridge_entryInvAt2 sources p den hden k r scratch n x bits hp E hwhole hFo hcnt hKlow hK0 hK0c h15 h17 h18 h284
    ph ph' hph A H A' H' hI2 hframe hheads hprot, ?_, ?_⟩
  · -- the phase words
    obtain ⟨-, -, -, -, hfut⟩ := hPW
    have hwd : ∀ ph'' : Phase, LaterPhase ph ph'' → ∀ i : Fin 278, (i.val = 81 ∨ i.val = 90) →
        laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A' (Wd sources p k r scratch ph'' i) = A (Wd sources p k r scratch ph'' i) := by
      intro ph'' hl i hi
      have hnc : ∀ j, Wd sources p k r scratch ph'' i ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) j := by
        have hk := keeps_later sources p k r scratch ph ph'' hl i hi
        have hw := wd_cases sources p k r scratch ph'' i
        intro j
        apply not_cache_of sources p k r scratch _ _
        right
        have hi' := (C10TailUniformSlots.phaseIndex ph'').isLt
        have hne : (C10TailUniformSlots.phaseIndex ph'').val ≠ 0 := by
          rcases hl with ⟨-, rfl | rfl⟩ | ⟨-, rfl⟩ <;> decide
        rcases hw with h | h | h | h <;> omega
      rw [laterA0_off sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A' _ hnc]
      exact hkeepA _ (keeps_later sources p k r scratch ph ph'' hl i hi)
    obtain ⟨f81, f90, fh81, fh90⟩ := hfut ph' hLph
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hwd ph' hLph 81 (Or.inl rfl), f81, prefixEntries_zero]; rfl
    · rw [hwd ph' hLph 90 (Or.inr rfl), f90, prefixEntries_zero]; rfl
    · show H' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Wd sources p k r scratch ph' 81)) = 0
      rw [hheads]; exact fh81
    · show H' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Wd sources p k r scratch ph' 90)) = 0
      rw [hheads]; exact fh90
    · intro ph'' hl''
      have hl : LaterPhase ph ph'' := by
        rcases hph with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hl'' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> first
          | (simp at h1; done) | exact Or.inl ⟨rfl, Or.inr h2⟩
      obtain ⟨g81, g90, gh81, gh90⟩ := hfut ph'' hl
      refine ⟨by rw [hwd ph'' hl 81 (Or.inl rfl)]; exact g81, by rw [hwd ph'' hl 90 (Or.inr rfl)]; exact g90, ?_, ?_⟩
      · show H' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Wd sources p k r scratch ph'' 81)) = 0
        rw [hheads]; exact gh81
      · show H' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Wd sources p k r scratch ph'' 90)) = 0
        rw [hheads]; exact gh90
  · -- the emitter/appender words: every `encT` is at or above `F`
    intro _
    obtain ⟨eH, eW, eA, ⟨w, hw, h5⟩⟩ := hEW hphNC
    have hsite : ∀ y : Fin E.T, E.d.F ≤ y.val →
        queriedAt sources p den hden k r scratch n x bits hp 0 (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A') (E.whole y) = queriedAt sources p den hden k r scratch n x bits hp (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) A (E.whole y) ∧ H' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (E.whole y)) = H (E.whole y) := by
      intro y hy
      have hv : PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 ≤ (E.whole y).val := by rw [hwhole]; omega
      have hnc := not_cache_of sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) (E.whole y) (Or.inr (by omega))
      refine ⟨?_, hheads _⟩
      rw [queriedAt_off sources p den hden k r scratch n x bits hp 0 _ _ hnc,
        laterA0_off sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A' _ hnc,
        queriedAt_off sources p den hden k r scratch n x bits hp _ A _ hnc]
      exact hkeepA _ (keeps_high sources p k r scratch ph _ hv)
    have hF : ∀ kk : Fin 13, E.d.F ≤ (Dims.encT (d := E.d) (E.pl ph').hT kk).val := fun kk => by
      simp only [Dims.encT]; omega
    have ee : ∀ kk : Fin 13, Dims.encT (d := E.d) (E.pl ph').hT kk = Dims.encT (d := E.d) (E.pl ph).hT kk := fun _ => rfl
    refine ⟨fun kk => ?_, fun en old => ?_, fun en xs => ?_, ⟨w, hw, ?_⟩⟩
    · show H' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (E.whole (Dims.encT (d := E.d) (E.pl ph').hT kk))) = 0
      rw [(hsite _ (hF kk)).2, ee]; exact eH kk
    · obtain ⟨a3, a7, a8, a9, a10⟩ := eW en old
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · show queriedAt sources p den hden k r scratch n x bits hp 0 (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A') (E.whole (Dims.encT (d := E.d) (E.pl ph').hT 3)) = _
        rw [(hsite _ (hF 3)).1, ee]; exact a3
      · show queriedAt sources p den hden k r scratch n x bits hp 0 (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A') (E.whole (Dims.encT (d := E.d) (E.pl ph').hT 6)) = _
        rw [(hsite _ (hF 6)).1, ee]; exact a7
      · show queriedAt sources p den hden k r scratch n x bits hp 0 (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A') (E.whole (Dims.encT (d := E.d) (E.pl ph').hT 7)) = _
        rw [(hsite _ (hF 7)).1, ee]; exact a8
      · show queriedAt sources p den hden k r scratch n x bits hp 0 (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A') (E.whole (Dims.encT (d := E.d) (E.pl ph').hT 8)) = _
        rw [(hsite _ (hF 8)).1, ee]; exact a9
      · show queriedAt sources p den hden k r scratch n x bits hp 0 (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A') (E.whole (Dims.encT (d := E.d) (E.pl ph').hT 9)) = _
        rw [(hsite _ (hF 9)).1, ee]; exact a10
    · obtain ⟨b2, b4, b5⟩ := eA en xs
      refine ⟨?_, ?_, ?_⟩
      · show queriedAt sources p den hden k r scratch n x bits hp 0 (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A') (E.whole (Dims.encT (d := E.d) (E.pl ph').hT 10)) = _
        rw [(hsite _ (hF 10)).1, ee]; exact b2
      · show queriedAt sources p den hden k r scratch n x bits hp 0 (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A') (E.whole (Dims.encT (d := E.d) (E.pl ph').hT 11)) = _
        rw [(hsite _ (hF 11)).1, ee]; exact b4
      · show queriedAt sources p den hden k r scratch n x bits hp 0 (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A') (E.whole (Dims.encT (d := E.d) (E.pl ph').hT 12)) = _
        rw [(hsite _ (hF 12)).1, ee]; exact b5
    · show queriedAt sources p den hden k r scratch n x bits hp 0 (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A') (E.whole (Dims.encT (d := E.d) (E.pl ph').hT 5)) = _
      rw [(hsite _ (hF 5)).1, ee]; exact h5

end bridge3

end
end NearCubicWires.SourceSteps
end

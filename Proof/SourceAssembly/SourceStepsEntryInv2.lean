import Proof.SourceAssembly.SourceStepsEntryInv

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

section inv2
open NearCubicWires.SourceConstruction.InitRun

/-- **The query facts at the FIRST entry**: `QueryAt` without the query copy's length (the init clears `284`). -/
def QueryAt0 {T : Nat} (c15 q284 c17 c18 : Fin T) (C : Nat) (wq : List Bool) (H : Fin T → ℕ) (A : Fin T → List Bool) : Prop :=
  A c15 = wq ∧ A c17 = List.replicate C true ∧ A c18 = List.replicate (C+1) false ∧
  H c15 = 0 ∧ H q284 = 0 ∧ H c17 = 0 ∧ H c18 = 0

/-- **The program's first site entry, `v4`**: the residue block is `278..284` (length `≤ Ce`, heads `0`); every kept tape below `F` off that
block holds its kept value. -/
def FirstEntry4 {d : SourceConstruction.Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T)
    (q b Rc Ce : Nat) (Kc : Fin T → Prop) (K0 : Fin T → List Bool) (KH0 : Fin T → Nat) (cnt : Fin T)
    (H : Fin T → ℕ) (A : Fin T → List Bool) : Prop :=
  A (d.scr pl.hT 11) = [] ∧ A pl.ar = UnaryTemplate.tape q ∧ H pl.ar = 0 ∧ A pl.wd = List.replicate b true ∧ H pl.wd = 0 ∧
  (∀ x : Fin T, 278 ≤ x.val → x.val < 285 → (A x).length ≤ Ce ∧ H x = 0) ∧
  (∀ x : Fin T, d.F ≤ x.val → x.val < d.U → A x = [] ∧ H x = 0) ∧
  (∀ x, Kc x → x.val < d.F → (x.val < 278 ∨ 285 ≤ x.val) → A x = K0 x ∧ H x = KH0 x) ∧
  (A cnt).length ≤ Rc ∧ H cnt ≤ Rc

variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (den : Nat) (hden : 0 < den) (k r scratch n : Nat)
  (x : BitInput n) (bits : List Bool)
  (hp : P1Independent.CappedLegalAdmission.passed sources p
    (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
    (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)

open Classical in
/-- **THE CLAUSE-ENTRY INVARIANT INSTANCE, v2** (`StepsContract2.Inv`): at (penalty, clause 0) the first-entry query facts and `FirstEntry4`;
everywhere else `QueryAt` and `LaterEntry`; all at `Hs = H ∘ whole`, `As = queriedAt ci A ∘ whole`. -/
def entryInvAt2 (E : EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (ph : Phase) (ci : Nat)
    (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (H : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) : Prop :=
  if ph = .penalty ∧ ci = 0 then
    QueryAt0 E.c15 E.q284 E.c17 E.c18 (capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) (ZeroPadding.pad (capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) (qwordAt sources p k n x bits ci))
      (fun i => H (E.whole i)) (fun i => queriedAt sources p den hden k r scratch n x bits hp ci A (E.whole i)) ∧
    FirstEntry4 (E.pl ph) E.q E.b E.Rc E.Ce E.Kc (E.K0 ph ci) E.KH0 E.cnt
      (fun i => H (E.whole i)) (fun i => queriedAt sources p den hden k r scratch n x bits hp ci A (E.whole i))
  else
    InitS.QueryAt E.c15 E.q284 E.c17 E.c18 (capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) (ZeroPadding.pad (capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) (qwordAt sources p k n x bits ci))
      (fun i => H (E.whole i)) (fun i => queriedAt sources p den hden k r scratch n x bits hp ci A (E.whole i)) ∧
    InitS.LaterEntry (E.pl ph) E.e E.Rc E.Rk E.Kc (E.K0 ph ci) E.KH0 E.cnt E.b E.q E.Mb E.Ms E.S E.Rw E.B E.U0
      (fun i => H (E.whole i)) (fun i => queriedAt sources p den hden k r scratch n x bits hp ci A (E.whole i))

/-- At (penalty, clause 0) `entryInvAt2` is the first-entry pair. -/
theorem entryInvAt2_first (E : EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (H : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
    (hQ : QueryAt0 E.c15 E.q284 E.c17 E.c18 (capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) (ZeroPadding.pad (capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) (qwordAt sources p k n x bits 0))
      (fun i => H (E.whole i)) (fun i => queriedAt sources p den hden k r scratch n x bits hp 0 A (E.whole i)))
    (hF : FirstEntry4 (E.pl .penalty) E.q E.b E.Rc E.Ce E.Kc (E.K0 .penalty 0) E.KH0 E.cnt
      (fun i => H (E.whole i)) (fun i => queriedAt sources p den hden k r scratch n x bits hp 0 A (E.whole i))) :
    entryInvAt2 sources p den hden k r scratch n x bits hp E .penalty 0 A H := by
  unfold entryInvAt2
  rw [if_pos ⟨rfl, rfl⟩]
  exact ⟨hQ, hF⟩

/-- Off (penalty, clause 0) `entryInvAt2` is the later pair (read). -/
theorem entryInvAt2_later_of (E : EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (ph : Phase) (ci : Nat)
    (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (H : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
    (h : entryInvAt2 sources p den hden k r scratch n x bits hp E ph ci A H) (hne : ¬ (ph = .penalty ∧ ci = 0)) :
    InitS.QueryAt E.c15 E.q284 E.c17 E.c18 (capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) (ZeroPadding.pad (capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) (qwordAt sources p k n x bits ci))
      (fun i => H (E.whole i)) (fun i => queriedAt sources p den hden k r scratch n x bits hp ci A (E.whole i)) ∧
    InitS.LaterEntry (E.pl ph) E.e E.Rc E.Rk E.Kc (E.K0 ph ci) E.KH0 E.cnt E.b E.q E.Mb E.Ms E.S E.Rw E.B E.U0
      (fun i => H (E.whole i)) (fun i => queriedAt sources p den hden k r scratch n x bits hp ci A (E.whole i)) := by
  unfold entryInvAt2 at h
  rw [if_neg hne] at h
  exact h

/-- Off (penalty, clause 0) `entryInvAt2` is the later pair (build). -/
theorem entryInvAt2_of_later (E : EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (ph : Phase) (ci : Nat)
    (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (H : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) (hne : ¬ (ph = .penalty ∧ ci = 0))
    (hQ : InitS.QueryAt E.c15 E.q284 E.c17 E.c18 (capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) (ZeroPadding.pad (capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) (qwordAt sources p k n x bits ci))
      (fun i => H (E.whole i)) (fun i => queriedAt sources p den hden k r scratch n x bits hp ci A (E.whole i)))
    (hL : InitS.LaterEntry (E.pl ph) E.e E.Rc E.Rk E.Kc (E.K0 ph ci) E.KH0 E.cnt E.b E.q E.Mb E.Ms E.S E.Rw E.B E.U0
      (fun i => H (E.whole i)) (fun i => queriedAt sources p den hden k r scratch n x bits hp ci A (E.whole i))) :
    entryInvAt2 sources p den hden k r scratch n x bits hp E ph ci A H := by
  unfold entryInvAt2
  rw [if_neg hne]
  exact ⟨hQ, hL⟩

/-- **THE BRIDGE on `entryInvAt2`** (`StepsContract2.bridge`'s exact type at `Inv := entryInvAt2 … E`), from the site-layout facts of `E`. -/
theorem bridge_entryInvAt2 (E : EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r scratch))
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
      entryInvAt2 sources p den hden k r scratch n x bits hp E ph (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) A H →
      (∀ t, (∀ j, Wd sources p k r scratch ph j ≠ t) → (∀ j, Fd sources p k r scratch ph j ≠ t) →
        A' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = A t) →
      (∀ t, H' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = H t) →
      (∀ i : Fin 218, (i = 0 ∨ i = 1 ∨ i = 216 ∨ i = 217) →
        A' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Fd sources p k r scratch ph (i.castAdd 1))) =
          A (Fd sources p k r scratch ph (i.castAdd 1))) →
      entryInvAt2 sources p den hden k r scratch n x bits hp E ph' 0 (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A')
        (fun i => H' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch i)) := by
  intro ph ph' hph A H A' H' hInv hframe hheads hprot
  have hNC := nc_pos sources p k n x bits
  have hphNC : ¬ (ph = .penalty ∧ NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) = 0) := fun h => absurd h.2 (Nat.pos_iff_ne_zero.mp hNC)
  have hph' : ¬ (ph' = .penalty ∧ (0 : Nat) = 0) := by
    rcases hph with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
  have hkeepA := keep_exit sources p k r scratch ph A A' hframe hprot
  have hold := entryInvAt2_later_of sources p den hden k r scratch n x bits hp E ph _ A H hInv hphNC
  exact entryInvAt2_of_later sources p den hden k r scratch n x bits hp E ph' 0 _ _ hph'
    (bridge_query sources p den hden k r scratch n x bits hp E ph hwhole h15 h17 h18 h284 A H A' H' hold.1 hkeepA hheads)
    (bridge_later sources p den hden k r scratch n x bits hp E ph ph' hwhole hFo hcnt hKlow (hK0 ph ph' hph)
      (fun y i hy hi => hK0c ph' 0 y i hy hi) A H A' H' hold.2 hkeepA hheads)

end inv2

end
end NearCubicWires.SourceSteps
end

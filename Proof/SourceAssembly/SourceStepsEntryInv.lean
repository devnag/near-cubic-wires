import Proof.SourceAssembly.SourceClauseBridgeR
import Proof.SourceAssembly.SourceSkelProt

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

/-! ## 1. The query install at a clause index -/

section query
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k n : Nat) (x : BitInput n) (bits : List Bool)

/-- **Clause `ci`'s query word** (`natListWord [left, right]` of its two literals), empty past the last clause. -/
def qwordAt (ci : Nat) : List Bool :=
  if h : ci < NC sources k (PolynomialClock.ordinaryClock k) x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) then
    natListWord [literalIndex (((CloseoutLanguage.selectedPCPP sources).output (req sources k (PolynomialClock.ordinaryClock k) x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))).clauses ⟨ci, h⟩).left,
      literalIndex (((CloseoutLanguage.selectedPCPP sources).output (req sources k (PolynomialClock.ordinaryClock k) x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))).clauses ⟨ci, h⟩).right]
  else []

/-- **The query cache at clause `ci`**: `clauseData … ci capC (qwordAt ci)`. -/
def cdAt (ci : Nat) : Fin 19 → List Bool :=
  PCPPQueryIndexPadding.clauseData (pcppOutput (req sources k (PolynomialClock.ordinaryClock k) x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))
      ((CloseoutLanguage.selectedPCPP sources).output (req sources k (PolynomialClock.ordinaryClock k) x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))))
    (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity ci
    (capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))
    (qwordAt sources p k n x bits ci)

theorem cdAt_15 (ci : Nat) :
    cdAt sources p k n x bits ci 15 =
      ZeroPadding.pad (capC sources k (PolynomialClock.ordinaryClock k) x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) (qwordAt sources p k n x bits ci) := by
  simp [cdAt, PCPPQueryIndexPadding.clauseData, PCPPQueryClauseReuse.data]

theorem cdAt_17 (ci : Nat) :
    cdAt sources p k n x bits ci 17 = List.replicate (capC sources k (PolynomialClock.ordinaryClock k) x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) true :=
  cd_17 _ _ _ _ _

theorem cdAt_18 (ci : Nat) :
    cdAt sources p k n x bits ci 18 = List.replicate (capC sources k (PolynomialClock.ordinaryClock k) x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) + 1) false :=
  cd_18 _ _ _ _ _

/-- The clause count is positive (`NC = 2^clauseBits`). -/
theorem nc_pos : 0 < NC sources k (PolynomialClock.ordinaryClock k) x
    (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) :=
  Nat.two_pow_pos _

end query

section queried
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (den : Nat) (hden : 0 < den) (k r scratch n : Nat)
  (x : BitInput n) (bits : List Bool)
  (hp : P1Independent.CappedLegalAdmission.passed sources p
    (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
    (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)

/-- **The site's queried bank at clause `ci`**: the cache holds `cdAt ci`. -/
def queriedAt (ci : Nat) (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) :
    Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool :=
  install (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp))
    A (cdAt sources p k n x bits ci)

/-- At a real clause, `queriedAt` IS `SourceTrace`'s `queried`. -/
theorem queriedAt_fin (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)))
    (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) :
    queriedAt sources p den hden k r scratch n x bits hp ci.val A =
      install (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp)) A
       (PCPPQueryIndexPadding.clauseData (pcppOutput (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) ((CloseoutLanguage.selectedPCPP sources).output (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)))) (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity ci.val
         (PCPPQueryCachedBounds.capacity (CloseoutLanguage.selectedPCPP sources) ((req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).circuit.size+(req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity))
         (natListWord [literalIndex (((CloseoutLanguage.selectedPCPP sources).output (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))).clauses ci).left,
           literalIndex (((CloseoutLanguage.selectedPCPP sources).output (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))).clauses ci).right])) := by
  unfold queriedAt cdAt qwordAt
  rw [dif_pos ci.isLt]

theorem queriedAt_cache (ci : Nat) (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (i : Fin 19) :
    queriedAt sources p den hden k r scratch n x bits hp ci A
      (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) =
      cdAt sources p k n x bits ci i :=
  install_slot _ (PCJ30aa6f1b7c2a4221_.Selected.cache_injective sources p k r scratch _) _ _ i

theorem queriedAt_off (ci : Nat) (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool)
    (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch))
    (ht : ∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) :
    queriedAt sources p den hden k r scratch n x bits hp ci A t = A t :=
  install_other _ _ _ _ (fun i he => ht i he.symm)

end queried

/-! ## 2. `FirstEntry3`, the site data, and `entryInvAt` -/

section inv
open NearCubicWires.SourceConstruction.InitRun

/-- **The site data of the clause-entry invariant** (R-SA31's parameters, `Ce` after `Rk`): the source layout `d`, the site universe `T` with
its embedding `whole` into the body, the per-phase placement (`wd = Wd ph 218`), the rest layout, the kept set with its per-`(phase, clause)`
values, the counter, the query tapes and the init's constants. -/
structure EntrySite (BT : Nat) where
  d : SourceConstruction.Dims
  eX : Nat
  pX : Nat
  gW : Nat
  eR : Nat
  eV : Nat
  X : Nat
  T : Nat
  whole : Fin T → Fin BT
  pl : Phase → Place d eX pX gW eR eV X T
  e : d.RestExt3 eX pX gW
  Rc : Nat
  Rk : Nat
  Ce : Nat
  Kc : Fin T → Prop
  K0 : Phase → Nat → Fin T → List Bool
  KH0 : Fin T → Nat
  cnt : Fin T
  c15 : Fin T
  q284 : Fin T
  c17 : Fin T
  c18 : Fin T
  b : Nat
  q : Nat
  Mb : Nat
  Ms : Nat
  S : Nat
  Rw : Nat
  B : Nat
  U0 : Nat

end inv

/-! ## 3. The cross-phase bridge on `entryInvAt` -/

section bridge
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (den : Nat) (hden : 0 < den) (k r scratch n : Nat)
  (x : BitInput n) (bits : List Bool)
  (hp : P1Independent.CappedLegalAdmission.passed sources p
    (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
    (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)

/-- The body offset is past the rewind block and the query copy. -/
theorem offset_ge_300 : 300 ≤ PCJda54a286946142d3_BranchPhases.offset sources p k r := by
  have hoff : PCJda54a286946142d3_BranchPhases.offset sources p k r =
      WorkspaceSelectedEntry.size sources k r p.clauseDegree + WorkspaceSelectedAdmission.originalTapes sources p k - 2 := rfl
  have hP : 302 ≤ WorkspaceSelectedEntry.size sources k r p.clauseDegree := by
    unfold WorkspaceSelectedEntry.size
    omega
  omega

/-- A tape in `[2, 302)` or at or above the offset is no cache tape. -/
theorem not_cache_of (mode : Bool) (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch))
    (h : (2 ≤ t.val ∧ t.val < 302) ∨ PCJda54a286946142d3_BranchPhases.offset sources p k r ≤ t.val) :
    ∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i := by
  intro i he
  have hc := cache_range sources p k r scratch mode i
  subst he
  have := offset_ge_300 sources p k r
  omega

/-- Every tape at or above `offset + 1155` is kept by every phase's fold. -/
theorem keeps_high (ph : Phase) (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch))
    (h : PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 ≤ t.val) : FoldKeeps sources p k r scratch ph t := by
  have hi := (C10TailUniformSlots.phaseIndex ph).isLt
  generalize hpi : (C10TailUniformSlots.phaseIndex ph).val = pi at hi
  generalize hoff : PCJda54a286946142d3_BranchPhases.offset sources p k r = o at h
  generalize htv : t.val = tv at h
  apply keeps_of sources p k r scratch ph t
  all_goals ((try simp only [hpi, hoff, htv]); omega)

/-- A fold-kept tape passes the phase exit (frame or protected premise). -/
theorem keep_exit (ph : Phase) (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (A' : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool)
    (hframe : ∀ t, (∀ j, Wd sources p k r scratch ph j ≠ t) → (∀ j, Fd sources p k r scratch ph j ≠ t) →
      A' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = A t)
    (hprot : ∀ i : Fin 218, (i = 0 ∨ i = 1 ∨ i = 216 ∨ i = 217) →
      A' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Fd sources p k r scratch ph (i.castAdd 1))) = A (Fd sources p k r scratch ph (i.castAdd 1)))
    (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (hk : FoldKeeps sources p k r scratch ph t) :
    A' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = A t := by
  rcases hk with ⟨hW, hF⟩ | ⟨i, hi, rfl⟩
  · exact hframe t hW hF
  · exact hprot i hi

/-- `LaterEntry` reads its placement only through `hT` (the site universe), so it moves between the phases' placements. -/
theorem laterEntry_place {d : SourceConstruction.Dims} {eX pX gW eR eV X T : Nat}
    (pl pl' : SourceConstruction.InitRun.Place d eX pX gW eR eV X T) {e : d.RestExt3 eX pX gW} {Rc Rk : Nat} {Kc : Fin T → Prop}
    {K0 : Fin T → List Bool} {KH0 : Fin T → Nat} {cnt : Fin T} {b q Mb Ms S Rw B U0 : Nat} {H : Fin T → ℕ} {A : Fin T → List Bool}
    (h : InitS.LaterEntry pl e Rc Rk Kc K0 KH0 cnt b q Mb Ms S Rw B U0 H A) :
    InitS.LaterEntry pl' e Rc Rk Kc K0 KH0 cnt b q Mb Ms S Rw B U0 H A := h

/-- The new query facts at the next phase's clause `0`. -/
theorem bridge_query (E : EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (ph : Phase)
    (hwhole : ∀ i, (E.whole i).val = i.val)
    (h15 : E.whole E.c15 = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) 15) (h17 : E.whole E.c17 = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) 17)
    (h18 : E.whole E.c18 = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) 18) (h284 : E.q284.val = 284)
    (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (H : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
    (A' : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool) (H' : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → Nat)
    (hQ : InitS.QueryAt E.c15 E.q284 E.c17 E.c18 (capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) (ZeroPadding.pad (capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) (qwordAt sources p k n x bits (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))))
      (fun i => H (E.whole i)) (fun i => queriedAt sources p den hden k r scratch n x bits hp (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) A (E.whole i)))
    (hkeepA : ∀ t, FoldKeeps sources p k r scratch ph t → A' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = A t)
    (hheads : ∀ t, H' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = H t) :
    InitS.QueryAt E.c15 E.q284 E.c17 E.c18 (capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) (ZeroPadding.pad (capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) (qwordAt sources p k n x bits 0))
      (fun i => H' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (E.whole i))) (fun i => queriedAt sources p den hden k r scratch n x bits hp 0 (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A') (E.whole i)) := by
  have hoff := offset_ge_300 sources p k r
  have hv : (E.whole E.q284).val = 284 := by rw [hwhole]; exact h284
  have hnc := not_cache_of sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) (E.whole E.q284) (Or.inl ⟨by omega, by omega⟩)
  have e284 : queriedAt sources p den hden k r scratch n x bits hp 0 (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A') (E.whole E.q284) = queriedAt sources p den hden k r scratch n x bits hp (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) A (E.whole E.q284) := by
    rw [queriedAt_off sources p den hden k r scratch n x bits hp 0 _ _ hnc,
      laterA0_off sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A' _ hnc,
      queriedAt_off sources p den hden k r scratch n x bits hp _ A _ hnc]
    exact hkeepA _ (mid_keeps sources p k r scratch ph _ (by omega) (by omega))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show queriedAt sources p den hden k r scratch n x bits hp 0 (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A') (E.whole E.c15) = _
    rw [h15, queriedAt_cache, cdAt_15]
  · show queriedAt sources p den hden k r scratch n x bits hp 0 (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A') (E.whole E.c17) = _
    rw [h17, queriedAt_cache, cdAt_17]
  · show queriedAt sources p den hden k r scratch n x bits hp 0 (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A') (E.whole E.c18) = _
    rw [h18, queriedAt_cache, cdAt_18]
  · show (queriedAt sources p den hden k r scratch n x bits hp 0 (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A') (E.whole E.q284)).length ≤ _
    rw [e284]
    exact hQ.2.2.2.1
  · show H' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (E.whole E.c15)) = 0
    rw [hheads]; exact hQ.2.2.2.2.1
  · show H' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (E.whole E.q284)) = 0
    rw [hheads]; exact hQ.2.2.2.2.2.1
  · show H' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (E.whole E.c17)) = 0
    rw [hheads]; exact hQ.2.2.2.2.2.2.1
  · show H' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (E.whole E.c18)) = 0
    rw [hheads]; exact hQ.2.2.2.2.2.2.2

/-- The new later entry at the next phase's clause `0`. -/
theorem bridge_later (E : EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (ph ph' : Phase)
    (hwhole : ∀ i, (E.whole i).val = i.val)
    (hFo : PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 ≤ E.d.F)
    (hcnt : E.d.F ≤ E.cnt.val)
    (hKlow : ∀ y, E.Kc y → y.val < E.d.F →
      (∃ i, E.whole y = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) ∨ y.val < 2 ∨ (278 ≤ y.val ∧ y.val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 124))
    (hK0 : ∀ y, E.Kc y → (∀ i, E.whole y ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) → E.K0 ph' 0 y = E.K0 ph (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) y)
    (hK0c : ∀ y i, E.Kc y → E.whole y = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i → E.K0 ph' 0 y = cdAt sources p k n x bits 0 i)
    (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (H : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
    (A' : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool) (H' : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → Nat)
    (hL : InitS.LaterEntry (E.pl ph) E.e E.Rc E.Rk E.Kc (E.K0 ph (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) E.KH0 E.cnt E.b E.q E.Mb E.Ms E.S E.Rw E.B E.U0
      (fun i => H (E.whole i)) (fun i => queriedAt sources p den hden k r scratch n x bits hp (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) A (E.whole i)))
    (hkeepA : ∀ t, FoldKeeps sources p k r scratch ph t → A' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = A t)
    (hheads : ∀ t, H' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = H t) :
    InitS.LaterEntry (E.pl ph') E.e E.Rc E.Rk E.Kc (E.K0 ph' 0) E.KH0 E.cnt E.b E.q E.Mb E.Ms E.S E.Rw E.B E.U0
      (fun i => H' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (E.whole i))) (fun i => queriedAt sources p den hden k r scratch n x bits hp 0 (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A') (E.whole i)) := by
  have hoff := offset_ge_300 sources p k r
  have hnew_off : ∀ t, (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) → queriedAt sources p den hden k r scratch n x bits hp 0 (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A') t = A' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) := by
    intro t ht
    rw [queriedAt_off sources p den hden k r scratch n x bits hp 0 _ t ht,
      laterA0_off sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A' t ht]
  have hold_off : ∀ t, (∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) → queriedAt sources p den hden k r scratch n x bits hp (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) A t = A t :=
    fun t ht => queriedAt_off sources p den hden k r scratch n x bits hp _ A t ht
  have hC := hL.2.2.1
  have hF : ∀ y : Fin E.T, E.d.F ≤ y.val →
      queriedAt sources p den hden k r scratch n x bits hp 0 (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A') (E.whole y) = queriedAt sources p den hden k r scratch n x bits hp (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) A (E.whole y) ∧ H' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (E.whole y)) = H (E.whole y) := by
    intro y hy
    have hv : PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 ≤ (E.whole y).val := by rw [hwhole]; omega
    have hnc := not_cache_of sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) (E.whole y) (Or.inr (by omega))
    refine ⟨?_, hheads _⟩
    rw [hnew_off _ hnc, hold_off _ hnc]
    exact hkeepA _ (keeps_high sources p k r scratch ph _ hv)
  have hK : ∀ y, E.Kc y → queriedAt sources p den hden k r scratch n x bits hp 0 (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A') (E.whole y) = E.K0 ph' 0 y ∧ H' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (E.whole y)) = E.KH0 y := by
    intro y hy
    refine ⟨?_, by rw [hheads]; exact (hC.kept y hy).2⟩
    by_cases hc : ∃ i, E.whole y = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i
    · obtain ⟨i, hi⟩ := hc
      rw [hi, queriedAt_cache]
      exact (hK0c y i hy hi).symm
    · have hnc : ∀ i, E.whole y ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i := fun i h => hc ⟨i, h⟩
      have hkeep : FoldKeeps sources p k r scratch ph (E.whole y) := by
        by_cases hyF : E.d.F ≤ y.val
        · exact keeps_high sources p k r scratch ph _ (by rw [hwhole]; omega)
        · rcases hKlow y hy (by omega) with h | h | h
          · exact absurd h hc
          · exact low_keeps sources p k r scratch ph _ (by rw [hwhole]; exact h)
          · exact mid_keeps sources p k r scratch ph _ (by rw [hwhole]; exact h.1) (by rw [hwhole]; exact h.2)
      rw [hnew_off _ hnc, hkeepA _ hkeep, ← hold_off _ hnc]
      exact ((hC.kept y hy).1).trans (hK0 y hy hnc).symm
  exact laterEntry_place (E.pl ph) (E.pl ph') (InitS.laterEntry_transfer hL hcnt hF hK)

end bridge

end
end NearCubicWires.SourceSteps
end

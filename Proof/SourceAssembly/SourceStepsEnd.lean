import Proof.SourceAssembly.SourceStepsClause

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest NearCubicWires.SourceConstruction.Bridge
open NearCubicWires.SourceSkeleton NearCubicWires.SourceParent NearCubicWires.SourcePhase
namespace NearCubicWires.SourceSteps
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

section clause
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources)
  (res : Nat) (hres : 19 ≤ res) {gamma : Real} (p : Parameters sources gamma) (k r : Nat)
  (ph : Phase)
  (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) (PacketsGlue.RequestMeta.seedCount (decompositionOf sources)))
  (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources))) {gW : Nat}
  (e : (dimsOf mask packets rows sources res p k r).RestExt3 se.extra sp.extra gW)
  (g7F : Phase → Σ s, Machine (UOf mask packets rows sources res p k r) s)
  (preFF : Phase → Σ s, Machine (UOf mask packets rows sources res p k r + 1) s)
  (compiler : Packets.CompilerLaws) (den : Nat) (hden : 0 < den) (n : Nat) (x : BitInput n) (bits : List Bool)
  (hp : P1Independent.CappedLegalAdmission.passed sources p
    (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
    (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
  (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)) states)
  (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)))
  (L Rc Rk : Nat)
  (lay : TraceData.LayoutFamily (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp) selector)
  (K : Fin (UOf mask packets rows sources res p k r) → Prop)
  (K0 : Fin (UOf mask packets rows sources res p k r) → List Bool)
  (KH0 : Fin (UOf mask packets rows sources res p k r) → Nat)
  (V : Nat) (dflt : P1TopDownPaidReusable.Datum)
  (Hd : Nat → Fin (UOf mask packets rows sources res p k r) → Nat) (Ad : Nat → Fin (UOf mask packets rows sources res p k r) → List Bool)
  (familyCost firstCost counterReserve refillCost : Nat)
  (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)) → List Bool)
  (H : Fin (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)) → Nat)
  (H' : Fin (UOf mask packets rows sources res p k r + 1) → Nat) (A' : Fin (UOf mask packets rows sources res p k r + 1) → List Bool)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r
set_option hygiene false in
local notation "𝒽" => UOf_le mask packets rows sources res p k r
set_option hygiene false in
local notation "𝒞" => skelCodeR mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph)
set_option hygiene false in
local notation "codeF" => fun ph' => skelCodeR mask packets rows sources res hres p k r ph' (refill3 mask packets rows sources res p k r se sp e (g7F ph').2) (preFF ph')
set_option hygiene false in
local notation "oracleC" => C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits
set_option hygiene false in
local notation "coordC" => PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x oracleC bits
set_option hygiene false in
local notation "tgtC" => C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)
set_option hygiene false in
local notation "modeC" => PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp
set_option hygiene false in
local notation "vQ" => (req sources k (PolynomialClock.ordinaryClock k) x oracleC).arity
set_option hygiene false in
local notation "layA" => layoutAtOf sources selector coordC ph ci L tgtC modeC lay
set_option hygiene false in
local notation "factsA" => factsAtOf sources selector compiler coordC ph ci L tgtC modeC
set_option hygiene false in
local notation "vWS" => P1TopDownPaidReusableReserves.workspace (printerOf sources) V
set_option hygiene false in
local notation "vRW" => P1TopDownPaidReusableReserves.rewind (printerOf sources) V
set_option hygiene false in
local notation "vBF" => P1TopDownPaidReusableReserves.buffer V
set_option hygiene false in
local notation "vMB" => InitRun.Mb L vQ
set_option hygiene false in
local notation "vMS" => InitPost.Ms L vQ
set_option hygiene false in
local notation "vU0" => InitRun.U0 L vQ
set_option hygiene false in
local notation "bS" => C10PartsSchedule.entryWidthSchedule sources k r n
set_option hygiene false in
local notation "w0S" => (A ((𝒞).whole (Dims.encT (d := 𝔇) 𝒽 5).castSucc)).take (InitRun.D0 bS)
set_option hygiene false in
local notation "oldS" => fun j => if j = 0 then w0S else oldAt coordC ph ci sources L tgtC modeC bS (InitRun.D0 bS) j
set_option hygiene false in
local notation "vdS" => clauseVals mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt (InitRun.D0 bS) (InitRun.cap0 bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS) oldS Hd Ad Rc familyCost refillCost firstCost counterReserve
set_option hygiene false in
local notation "NS" => (vdS).entries.length
set_option hygiene false in
local notation "Inv5S" => Inv5 mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc Rk bS lay K K0 KH0 V dflt (InitRun.D0 bS) (InitRun.cap0 bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS) (CloseoutFinalC10AppendWorkspaceInit.capacity bS) Hd Ad oldS familyCost firstCost counterReserve refillCost Rc Rc Rc Rc NS H' A'
set_option hygiene false in
local notation "H0cS" => (fun y : Fin (UOf mask packets rows sources res p k r) => H' y.castSucc)
set_option hygiene false in
local notation "A0cS" => chainView 𝒞 bS vdS NS 0 (fun y : Fin (UOf mask packets rows sources res p k r) => A' y.castSucc)
set_option hygiene false in
local notation "CSP" => ChainStartP mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc Rk bS lay K K0 KH0 V dflt Hd Ad familyCost firstCost counterReserve refillCost Rc Rc Rc Rc w0S A H H' A'
set_option hygiene false in
local notation "BTS" => ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)
set_option hygiene false in
local notation "OFFS" => PCJda54a286946142d3_BranchPhases.offset sources p k r
set_option hygiene false in
local notation "CACHES" => PCJda54a286946142d3_BranchPhases.cache sources p k r (scratchOf mask packets rows sources res) modeC
set_option hygiene false in
local notation "RF" => refill3 mask packets rows sources res p k r se sp e (g7F ph).2

set_option hygiene false in
local notation "VVS" => chainVals 𝒞 bS vdS seam H0cS A0cS
set_option hygiene false in
local notation "INV" => Nat → (Fin (UOf mask packets rows sources res p k r) → Nat) → (Fin (UOf mask packets rows sources res p k r) → List Bool) → Prop

/-- The slots are never `encT` tapes. -/
theorem encNS_S (kk : Fin 13) (i : Fin (r_tapes (𝒞).a)) : (𝒞).slots i ≠ Dims.encT (d := 𝔇) 𝒽 kk := by
  intro h
  have hv := congrArg Fin.val h
  rw [(𝒞)._hs, encT_val_R mask packets rows sources res p k r] at hv
  have hi := i.isLt
  have ha : r_tapes (𝒞).a = r_tapes (printerOf sources) := rfl
  omega

/-- The emitter's `encT 6..9` are `enc 7..10`. -/
theorem encT_readHi (A : Fin (UOf mask packets rows sources res p k r) → List Bool) (E : Fin 11 → List Bool) (T : Fin 6 → List Bool)
    (kk : Fin 13) (h6 : 6 ≤ kk.val) (h9 : kk.val ≤ 9) :
    install (𝒞).app (install (𝒞).enc A E) T (Dims.encT (d := 𝔇) 𝒽 kk) = E ⟨kk.val + 1, Nat.lt_of_le_of_lt (Nat.succ_le_succ h9) (by decide)⟩ := by
  have he : (𝒞).enc ⟨kk.val + 1, by omega⟩ = Dims.encT (d := 𝔇) 𝒽 kk := by
    apply Fin.ext
    rw [enc_val_R mask packets rows sources res hres p k r ph RF (preFF ph) ⟨kk.val + 1, by omega⟩ (by show kk.val + 1 ≠ 5; omega),
      encT_val_R mask packets rows sources res p k r]
    simp only
    rw [if_neg (by omega)]
    omega
  have ha' : ∀ i, (𝒞).app i ≠ Dims.encT (d := 𝔇) 𝒽 kk := by
    intro i h
    have hv := congrArg Fin.val h
    rw [encT_val_R mask packets rows sources res p k r] at hv
    have hF : (𝔇).F = OFFS + 1155 := rfl
    rcases happP_R mask packets rows sources res hres p k r ph RF (preFF ph) i with hlo | ⟨hhi, -⟩
    · omega
    · rcases app_high2 mask packets rows sources res hres p k r ph se sp e g7F preFF i hhi with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ <;> omega
  exact (install_other (𝒞).app (install (𝒞).enc A E) T _ ha').trans
    (he ▸ install_slot _ (enc_injective_R mask packets rows sources res hres p k r ph RF (preFF ph)) A E ⟨kk.val + 1, by omega⟩)

/-- An `app` tape that is an `encT` tape reads the appender's word. -/
theorem appEncT (X : Fin (UOf mask packets rows sources res p k r) → List Bool) (T : Fin 6 → List Bool) (i : Fin 6) (kk : Fin 13)
    (h : ((𝒞).app i).val = (Dims.encT (d := 𝔇) 𝒽 kk).val) :
    install (𝒞).app X T (Dims.encT (d := 𝔇) 𝒽 kk) = T i := by
  have hh : (𝒞).app i = Dims.encT (d := 𝔇) 𝒽 kk := Fin.ext h
  exact (congrArg (install (𝒞).app X T) hh).symm.trans
    (install_slot _ (app_injective_R mask packets rows sources res hres p k r ph RF (preFF ph)) X T i)

/-- `EncWords` reads only the `encT` tapes. -/
theorem encWords_congr {d : SourceConstruction.Dims} {T T' : Nat} (hT : d.U ≤ T) (hT' : d.U ≤ T') (Rc' b' : Nat)
    (H1 : Fin T → ℕ) (A1 : Fin T → List Bool) (H2 : Fin T' → ℕ) (A2 : Fin T' → List Bool)
    (hH : ∀ kk, H1 (Dims.encT (d := d) hT kk) = H2 (Dims.encT (d := d) hT' kk))
    (hA : ∀ kk, A1 (Dims.encT (d := d) hT kk) = A2 (Dims.encT (d := d) hT' kk))
    (h : EncWords hT' Rc' b' H2 A2) : EncWords hT Rc' b' H1 A1 := by
  obtain ⟨h1, h2, h3, ⟨w, hw, hw5⟩⟩ := h
  refine ⟨fun kk => (hH kk).trans (h1 kk), fun en old => ?_, fun en xs => ?_, ⟨w, hw, (hA 5).trans hw5⟩⟩
  · obtain ⟨a1, a2, a3, a4, a5⟩ := h2 en old
    exact ⟨(hA 3).trans a1, (hA 6).trans a2, (hA 7).trans a3, (hA 8).trans a4, (hA 9).trans a5⟩
  · obtain ⟨a1, a2, a3⟩ := h3 en xs
    exact ⟨(hA 10).trans a1, (hA 11).trans a2, (hA 12).trans a3⟩

/-- At a clause with no call the chain's end is its start: on `encT` it reads the first cycle's exit. -/
theorem end_zero_encT (Inv : INV) (seam : SeamSpec NS (fun _ => 0) (𝒞).slots (inTOf 𝒞 bS vdS) Inv (goodOf 𝒞 bS vdS)) (hz : NS = 0) (kk : Fin 13) :
    (VVS).H NS (Dims.encT (d := 𝔇) 𝒽 kk) = H' (Dims.encT (d := 𝔇) (UOf_le_succ mask packets rows sources res p k r) kk) ∧
    (VVS).A NS (Dims.encT (d := 𝔇) 𝒽 kk) = A' (Dims.encT (d := 𝔇) (UOf_le_succ mask packets rows sources res p k r) kk) := by
  have hc := chain_zero_S mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc lay V dflt Hd Ad
    familyCost firstCost counterReserve refillCost A H' A' Inv seam NS hz
  have hH0 : (VVS).H NS = H0cS := congrArg Prod.fst hc
  have hA0 : (VVS).A NS = A0cS := congrArg Prod.snd hc
  have hcs := encT_castSucc mask packets rows sources res p k r kk
  have hv : A0cS (Dims.encT (d := 𝔇) 𝒽 kk) = A' (Dims.encT (d := 𝔇) 𝒽 kk).castSucc := by
    rw [chainView_ge 𝒞 bS vdS NS 0 (Nat.le_of_eq hz)]
    exact install_other _ _ _ _ (fun i => encNS_S mask packets rows sources res hres p k r ph se sp e g7F preFF kk i)
  exact ⟨(congrFun hH0 _).trans (congrArg H' hcs), ((congrFun hA0 _).trans hv).trans (congrArg A' hcs)⟩

/-- **The chain END's `encT` words** (`NextHole`'s `EncWords`): `Inv5` conjuncts 4, 6 at `N > 0`; the first cycle's exit (`ChainStartP` (5)) at `N = 0`. -/
theorem encWordsEnd_S (hS : CSP) (Inv : INV) (hInv : ∀ j Hc Ac, Inv j Hc Ac → Inv5S j Hc Ac)
    (seam : SeamSpec NS (fun _ => 0) (𝒞).slots (inTOf 𝒞 bS vdS) Inv (goodOf 𝒞 bS vdS)) (h0 : Inv 0 H0cS A0cS) :
    EncWords 𝒽 Rc bS ((VVS).H NS) ((VVS).A NS) := by
  have hE := end_S mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc Rk lay K K0 KH0 V dflt Hd Ad
    familyCost firstCost counterReserve refillCost A H' A' Inv hInv seam h0
  unfold Inv5 at hE
  obtain ⟨-, -, -, h4, -, h6⟩ := hE
  have hS' := hS
  unfold ChainStartP at hS'
  obtain ⟨-, -, -, -, -, -, -, -, hEW⟩ := hS'
  by_cases hN : 0 < NS
  · have hH : ∀ kk, (VVS).H NS (Dims.encT (d := 𝔇) 𝒽 kk) = 0 := fun kk =>
      (h4 kk).trans ((congrArg H' (encT_castSucc mask packets rows sources res p k r kk)).trans (hEW.1 kk))
    have hw := h6 (Nat.le_refl _) hN
    refine ⟨hH, fun en old => ?_, fun en xs => ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hw 3 (Or.inl rfl), encT_read mask packets rows sources res hres p k r ph RF (preFF ph) _ _ _ 3 (by decide)]
        exact congrArg (ZeroPadding.pad Rc) (ebank_indep _ _ _ _ _ _ _ _ (Or.inl rfl))
      · rw [hw 6 (Or.inr (by decide)), encT_readHi mask packets rows sources res hres p k r ph se sp e g7F preFF _ _ _ 6 (by decide) (by decide)]
        exact congrArg (ZeroPadding.pad Rc) (ebank_indep _ _ _ _ _ _ _ _ (Or.inr (by decide)))
      · rw [hw 7 (Or.inr (by decide)), encT_readHi mask packets rows sources res hres p k r ph se sp e g7F preFF _ _ _ 7 (by decide) (by decide)]
        exact congrArg (ZeroPadding.pad Rc) (ebank_indep _ _ _ _ _ _ _ _ (Or.inr (by decide)))
      · rw [hw 8 (Or.inr (by decide)), encT_readHi mask packets rows sources res hres p k r ph se sp e g7F preFF _ _ _ 8 (by decide) (by decide)]
        exact congrArg (ZeroPadding.pad Rc) (ebank_indep _ _ _ _ _ _ _ _ (Or.inr (by decide)))
      · rw [hw 9 (Or.inr (by decide)), encT_readHi mask packets rows sources res hres p k r ph se sp e g7F preFF _ _ _ 9 (by decide) (by decide)]
        exact congrArg (ZeroPadding.pad Rc) (ebank_indep _ _ _ _ _ _ _ _ (Or.inr (by decide)))
    · refine ⟨?_, ?_, ?_⟩
      · rw [hw 10 (Or.inr (by decide)), appEncT mask packets rows sources res hres p k r ph se sp e g7F preFF _ _ 2 10
          (by rw [encT_val_R mask packets rows sources res p k r]; rfl)]
        rfl
      · rw [hw 11 (Or.inr (by decide)), appEncT mask packets rows sources res hres p k r ph se sp e g7F preFF _ _ 4 11
          (by rw [encT_val_R mask packets rows sources res p k r]; rfl)]
        rfl
      · rw [hw 12 (Or.inr (by decide)), appEncT mask packets rows sources res hres p k r ph se sp e g7F preFF _ _ 5 12
          (by rw [encT_val_R mask packets rows sources res p k r]; rfl)]
        rfl
    · rw [hw 5 (Or.inr (by decide)), appEncT mask packets rows sources res hres p k r ph se sp e g7F preFF _ _ 0 5
        (by rw [encT_val_R mask packets rows sources res p k r]; rfl)]
      refine ⟨_, ?_, rfl⟩
      show (ZeroPadding.pad (InitRun.D0 bS) (Stream.entryWord bS _)).length ≤ InitRun.D0 bS
      rw [ZeroPadding.pad_length, CloseoutFinalC10SiteRoundPorts.entryWord_length]
      simp only [InitRun.D0, InitEnc.rr]
      omega
  · have hz : NS = 0 := by omega
    exact encWords_congr 𝒽 (UOf_le_succ mask packets rows sources res p k r) Rc bS _ _ H' A'
      (fun kk => (end_zero_encT mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc lay V dflt Hd Ad
        familyCost firstCost counterReserve refillCost A H' A' Inv seam hz kk).1)
      (fun kk => (end_zero_encT mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc lay V dflt Hd Ad
        familyCost firstCost counterReserve refillCost A H' A' Inv seam hz kk).2) hEW

theorem lenEnd_S
    (hS5 : ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → (A' (Dims.encT (d := 𝔇) (UOf_le_succ mask packets rows sources res p k r) kk)).length ≤ Rc)
    (Inv : INV) (seam : SeamSpec NS (fun _ => 0) (𝒞).slots (inTOf 𝒞 bS vdS) Inv (goodOf 𝒞 bS vdS)) (h0 : Inv 0 H0cS A0cS)
    (h7 : ∀ Hc Ac, Inv NS Hc Ac → 0 < NS → ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → (Ac (Dims.encT (d := 𝔇) 𝒽 kk)).length ≤ Rc) :
    ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → ((VVS).A NS (Dims.encT (d := 𝔇) 𝒽 kk)).length ≤ Rc := by
  intro kk hk
  by_cases hN : 0 < NS
  · exact h7 _ _ (callChain_inv seam H0cS A0cS h0 NS le_rfl) hN kk hk
  · exact (congrArg List.length (end_zero_encT mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc lay V dflt Hd Ad
      familyCost firstCost counterReserve refillCost A H' A' Inv seam (by omega) kk).2).trans_le (hS5 kk hk)

end clause

end
end NearCubicWires.SourceSteps
end


import Proof.SourceAssembly.SourceStepsEntryInv4
import Proof.SourceAssembly.SourceStepsFirstOut

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
open NearCubicWires.SourceSkeleton NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceSteps
namespace NearCubicWires.SourceSkeleton.StartB
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

section start
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources)
  (res : Nat) (hres : 19 ≤ res) {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r
set_option hygiene false in
local notation "𝒽" => UOf_le mask packets rows sources res p k r
set_option hygiene false in
local notation "𝒽1" => UOf_le_succ mask packets rows sources res p k r
set_option hygiene false in
local notation "preFF" => fun ph' => (⟨_, Rest.firstPro3 se sp e (UOf_le_succ mask packets rows sources res p k r) (initF ph').2 (g7G ph').2 cnt c15 q284 c17 c18⟩ :
  Σ s, Machine (UOf mask packets rows sources res p k r + 1) s)
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
local notation "vdS" => clauseVals mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt (InitRun.D0 b) (InitRun.cap0 b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) (fun j => if j = 0 then w0 else oldAt coordC ph ci sources L tgtC modeC b (InitRun.D0 b) j) Hd Ad Rc familyCost refillCost firstCost counterReserve
set_option hygiene false in
local notation "𝔄0" => fun i => queriedAt sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp ci.val A ((𝒞).whole i)
set_option hygiene false in
local notation "ℌ0" => fun i => H ((𝒞).whole i)
set_option hygiene false in
local notation "ℭ" => PCJda54a286946142d3_BranchPhases.cache sources p k r (scratchOf mask packets rows sources res) modeC

/-- The pad by `0` is the identity. -/
theorem pad_zero (w : List Bool) : ZeroPadding.pad 0 w = w := by
  simp [ZeroPadding.pad]

section tapes
variable (ph : Phase) (refill : Σ s, Machine (UOf mask packets rows sources res p k r) s)
  (preF : Σ s, Machine (UOf mask packets rows sources res p k r + 1) s)

set_option hygiene false in
local notation "𝒞'" => skelCodeR mask packets rows sources res hres p k r ph refill preF

/-- `encT kk` on `U + 1` sits at `F + rt + kk`. -/
theorem encT1_val (kk : Fin 13) :
    (Dims.encT (d := 𝔇) 𝒽1 kk).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 + r_tapes (printerOf sources) + kk.val := by
  simp only [Dims.encT, dimsOf]

/-- `encT kk` on `U` and on `U + 1` are the same tape. -/
theorem encT_cs (kk : Fin 13) : (Dims.encT (d := 𝔇) 𝒽 kk).castSucc = Dims.encT (d := 𝔇) 𝒽1 kk := Fin.ext rfl

/-- `enc i` (`i < 5`) is `encT i`. -/
theorem enc_lo (i : Fin 11) (h : i.val < 5) : ((𝒞').enc i).castSucc = Dims.encT (d := 𝔇) 𝒽1 ⟨i.val, by omega⟩ := by
  have e := enc_eq_encT mask packets rows sources res hres p k r ph refill preF ⟨i.val, by omega⟩ h
  have ei : (⟨i.val, by omega⟩ : Fin 11) = i := Fin.ext rfl
  rw [ei] at e
  rw [e]
  exact encT_cs mask packets rows sources res p k r _

/-- `enc i` (`6 ≤ i`) is `encT (i - 1)`. -/
theorem enc_hi (i : Fin 11) (h : 6 ≤ i.val) : ((𝒞').enc i).castSucc = Dims.encT (d := 𝔇) 𝒽1 ⟨i.val - 1, by omega⟩ := by
  apply Fin.ext
  have hv := enc_val_R mask packets rows sources res hres p k r ph refill preF i (by omega)
  rw [if_neg (by omega)] at hv
  rw [Fin.val_castSucc, hv, encT1_val]

/-- `app 2` is `encT 10`. -/
theorem app2_encT : ((𝒞').app 2).castSucc = Dims.encT (d := 𝔇) 𝒽1 10 := by
  apply Fin.ext
  rw [Fin.val_castSucc, encT1_val]
  show appVal mask packets rows sources res p k r ph 2 = _
  simp [appVal]

/-- `app 4` is `encT 11`. -/
theorem app4_encT : ((𝒞').app 4).castSucc = Dims.encT (d := 𝔇) 𝒽1 11 := by
  apply Fin.ext
  rw [Fin.val_castSucc, encT1_val]
  show appVal mask packets rows sources res p k r ph 4 = _
  simp [appVal]

/-- `app 5` is `encT 12`. -/
theorem app5_encT : ((𝒞').app 5).castSucc = Dims.encT (d := 𝔇) 𝒽1 12 := by
  apply Fin.ext
  rw [Fin.val_castSucc, encT1_val]
  show appVal mask packets rows sources res p k r ph 5 = _
  simp [appVal]

/-- The code's `whole` keeps the index of an `app` tape (`rfl`). -/
theorem whole_app_val (i : Fin 6) : ((𝒞').whole ((𝒞').app i).castSucc).val = ((𝒞').app i).val := rfl

/-- `app 1` is the phase word slot `Wd ph 81`. -/
theorem app1_wd : ((𝒞').app 1).val = (SourceParent.Wd sources p k r (scratchOf mask packets rows sources res) ph 81).val := rfl

/-- `app 3` is the phase count slot `Wd ph 90`. -/
theorem app3_wd : ((𝒞').app 3).val = (SourceParent.Wd sources p k r (scratchOf mask packets rows sources res) ph 90).val := rfl

end tapes

/-- **`ChainStartP` from the first seam's exit.** -/
theorem chainStart_first (ph : Phase)
    (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) (PacketsGlue.RequestMeta.seedCount (decompositionOf sources)))
    (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources))) {gW : Nat}
    (e : (𝔇).RestExt3 se.extra sp.extra gW)
    (g7F : Phase → Σ s, Machine (UOf mask packets rows sources res p k r) s)
    (initF g7G : Phase → Σ s, Machine (UOf mask packets rows sources res p k r + 1) s)
    (cnt c15 q284 c17 c18 : Fin (UOf mask packets rows sources res p k r + 1))
    (compiler : Packets.CompilerLaws) (den : Nat) (hden : 0 < den) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)) states)
    (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (L : Nat) (Rc Rk b : Nat)
    (lay : TraceData.LayoutFamily coordC ph ci sources L tgtC modeC selector)
    (K : Fin (UOf mask packets rows sources res p k r) → Prop)
    (K0 : Fin (UOf mask packets rows sources res p k r) → List Bool)
    (KH0 : Fin (UOf mask packets rows sources res p k r) → Nat)
    (K1 : Fin (UOf mask packets rows sources res p k r + 1) → Prop)
    (K01 : Fin (UOf mask packets rows sources res p k r + 1) → List Bool)
    (KH01 : Fin (UOf mask packets rows sources res p k r + 1) → Nat)
    (V : Nat) (dflt : P1TopDownPaidReusable.Datum)
    (Hd : Nat → Fin (UOf mask packets rows sources res p k r) → Nat) (Ad : Nat → Fin (UOf mask packets rows sources res p k r) → List Bool)
    (familyCost firstCost counterReserve refillCost : Nat) (w0 : List Bool)
    (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)) → List Bool)
    (H : Fin (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)) → Nat)
    (Hi H' : Fin (UOf mask packets rows sources res p k r + 1) → Nat) (Ai A' : Fin (UOf mask packets rows sources res p k r + 1) → List Bool)
    -- the first seam's exit
    (hfo : firstOutP mask packets rows sources res p k r se sp e 𝒽1 (initF ph).2 (g7G ph).2 coordC ph ci L tgtC modeC Rc Rk b layA factsA
      K1 K01 KH01 ((𝔇).maskSlots_injective 𝒽1) ((𝔇).pslots_injective 𝒽1) ((𝔇).familySlots_injective 𝒽1) ((𝔇).poolSlots_injective 𝒽1)
      (rewind2_injective e.ext2.ext1.ext 𝒽1) (hrawR mask packets rows sources res p k r 𝒽1) (hpoolR mask packets rows sources res p k r 𝒽1)
      (hsrcR mask packets rows sources res hres p k r 𝒽1) cnt c15 q284 c17 c18 (ℌ0) Hi (𝔄0) Ai
      b vMB vMS Rc Rc Rc Rc vWS vRW vBF b vU0 (fuelOf 𝒞 b vdS 0) firstCost H' A')
    -- the guard's exit
    (hlowG : ∀ y : Fin (UOf mask packets rows sources res p k r + 1), y.val < (𝔇).F → (y.val < 278 ∨ 284 ≤ y.val) →
      Ai y = (𝔄0) y ∧ Hi y = (ℌ0) y)
    (hEncI : SourceSteps.EncWords (d := 𝔇) 𝒽1 Rc b Hi Ai)
    (hpay : Ai (Dims.encT (d := 𝔇) 𝒽1 5) = ZeroPadding.pad Rc w0)
    -- the phase words at the entry
    (hW81 : queriedAt sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp ci.val A
      (SourceParent.Wd sources p k r (scratchOf mask packets rows sources res) ph 81) =
      CloseoutRowsEstimatorCoefficients.Stream.words b (prefixEntries (phaseE sources p den k x bits modeC ph L) ci.val))
    (hW90 : queriedAt sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp ci.val A
      (SourceParent.Wd sources p k r (scratchOf mask packets rows sources res) ph 90) =
      CompareMachine.word (prefixEntries (phaseE sources p den k x bits modeC ph L) ci.val).length)
    -- the query tapes
    (hc15 : ∀ y : Fin (UOf mask packets rows sources res p k r + 1), (∀ i, y.val ≠ (ℭ i).val) → y ≠ c15)
    (hq284 : q284.val = 284) (hcnt : cnt.val = (𝔇).U)
    (hWnc : ∀ i : Fin 6, ((𝒞).app i).val < (𝔇).F → ∀ j, ((𝒞).app i).val ≠ (ℭ j).val)
    
    (hlay : ∀ j, (lay j).degree = Admission.uniformDeg vQ L) (hL1 : 1 ≤ L)
    (hu : 1 ≤ vQ / (200 * (normalizedLiveCount vQ L + 1 + 1)))
    -- the kept sets (`first_startV`)
    (hKpos : ∀ y, K y → y.val < (𝔇).F ∨
      ((𝔇).B + 29 + restPc se.extra sp.extra gW ≤ y.val ∧ y ≠ Dims.hrT e 𝒽 10 ∧ y ≠ Dims.hrT e 𝒽 11))
    (hK : ∀ y, K y → K1 y.castSucc) (hK0 : ∀ y, K y → K01 y.castSucc = K0 y ∧ KH01 y.castSucc = KH0 y)
    (hKapp : ∀ y, K y → ∀ i, (𝒞).app i ≠ y)
    (hcR : counterReserve = Rc) :
    ChainStartP mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc Rk b lay K K0 KH0 V dflt Hd Ad
      familyCost firstCost counterReserve refillCost Rc Rc Rc Rc w0 A H H' A' := by
  obtain ⟨fPrep, fnatH, fnatA, ⟨fcA, fcH⟩, fInv, fencH, fenc4, fenc012, fencK, ffr, flong⟩ := hfo
  have hQ81 : (𝔄0) ((𝒞).app 1).castSucc = CloseoutRowsEstimatorCoefficients.Stream.words b (prefixEntries (phaseE sources p den k x bits modeC ph L) ci.val) := by
    have ew : (𝒞).whole ((𝒞).app 1).castSucc = SourceParent.Wd sources p k r (scratchOf mask packets rows sources res) ph 81 :=
      Fin.ext ((whole_app_val mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph) 1).trans (app1_wd mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph)))
    show queriedAt sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp ci.val A ((𝒞).whole ((𝒞).app 1).castSucc) = _
    rw [ew]; exact hW81
  have hQ90 : (𝔄0) ((𝒞).app 3).castSucc = CompareMachine.word (prefixEntries (phaseE sources p den k x bits modeC ph L) ci.val).length := by
    have ew : (𝒞).whole ((𝒞).app 3).castSucc = SourceParent.Wd sources p k r (scratchOf mask packets rows sources res) ph 90 :=
      Fin.ext ((whole_app_val mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph) 3).trans (app3_wd mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph)))
    show queriedAt sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp ci.val A ((𝒞).whole ((𝒞).app 3).castSucc) = _
    rw [ew]; exact hW90
  -- (1) the first cycle
  have hds0 := ds_bridge sources selector compiler coordC ph ci L tgtC modeC lay 0
  have p1 : MaskFamilyCode.Prepared (𝒞).firstCode ((vdS).ds 0) firstCost (ℌ0) H' (𝔄0) A' := by
    show MaskFamilyCode.Prepared (𝒞).firstCode (TraceData.dsOf coordC ph ci sources L tgtC modeC selector compiler lay 0) firstCost (ℌ0) H' (𝔄0) A'
    rw [hds0]
    exact fPrep
  -- (5) the emitter/appender words carried through the first seam
  obtain ⟨eH, eE, eA, eP⟩ := hEncI
  have p5 : SourceSteps.EncWords (d := 𝔇) 𝒽1 Rc b H' A' := by
    refine ⟨fun kk => (fencH kk).trans (eH kk), fun en old => ?_, fun en xs => ?_, ?_⟩
    · rw [fencK 3 (Or.inl rfl), fencK 6 (Or.inr (by decide)), fencK 7 (Or.inr (by decide)), fencK 8 (Or.inr (by decide)),
        fencK 9 (Or.inr (by decide))]
      exact eE en old
    · rw [fencK 10 (Or.inr (by decide)), fencK 11 (Or.inr (by decide)), fencK 12 (Or.inr (by decide))]
      exact eA en xs
    · rw [fencK 5 (Or.inr (by decide))]
      exact eP
  -- (4) the composite frame
  have p4 : ∀ y : Fin (𝒞).sourceTapes, y.val < (𝔇).F →
      Cycle.Free ((𝔇).slot 𝒽) ((𝔇).maskSlots 𝒽) ((𝔇).pslots 𝒽) ((𝔇).poolSlots 𝒽) ((𝔇).familySlots 𝒽)
        (Dims.rewind2Slots e.ext2.ext1.ext 𝒽) y →
      (∀ i, y.val ≠ (ℭ i).val) → (y.val < 278 ∨ 284 < y.val) →
      A' y.castSucc = (𝔄0) y.castSucc ∧ H' y.castSucc = (ℌ0) y.castSucc := by
    intro y hyF _ hyc hy
    have hfree := free_below e.ext2.ext1.ext 𝒽1 y.castSucc (by rw [Fin.val_castSucc]; omega) (by rw [Fin.val_castSucc]; omega)
      (by rw [Fin.val_castSucc]; exact hyF)
    obtain ⟨h1, h2⟩ := ffr y.castSucc (by rw [Fin.val_castSucc]; exact hyF) hfree
      (hc15 y.castSucc (fun i => by rw [Fin.val_castSucc]; exact hyc i))
      (fun h => by have := congrArg Fin.val h; rw [Fin.val_castSucc, hq284] at this; omega)
    obtain ⟨g1, g2⟩ := hlowG y.castSucc (by rw [Fin.val_castSucc]; exact hyF) (by rw [Fin.val_castSucc]; omega)
    exact ⟨h2.trans g1, h1.trans g2⟩
  -- (3) the seam words at call `0`
  have hencInj := enc_injective_R mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph)
  have happInj := app_injective_R mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph)
  have p3 : 0 < (vdS).entries.length →
      (∀ i, (∀ i', (𝒞).slots i' ≠ (𝒞).enc i) →
        chainView 𝒞 b vdS (vdS).entries.length 0 (fun y => A' y.castSucc) ((𝒞).enc i) = encInOf 𝒞 b vdS 0 i) ∧
      (∀ i, (∀ i', (𝒞).slots i' ≠ (𝒞).app i) → (∀ i', (𝒞).enc i' ≠ (𝒞).app i) →
        chainView 𝒞 b vdS (vdS).entries.length 0 (fun y => A' y.castSucc) ((𝒞).app i) = appInOf 𝒞 b vdS 0 i) := by
    intro hN
    rw [chainView_lt 𝒞 b vdS _ 0 hN]
    exact ⟨fun i hs => viewOf_enc 𝒞 b vdS hencInj 0 _ i hs, fun i hs he => viewOf_app 𝒞 b vdS happInj 0 _ i hs he⟩
  -- (2) the chain start in the exact view
  have hE0 : 0 < (vdS).entries.length → ∀ i, (∀ i', (𝒞).slots i' ≠ (𝒞).enc i) →
      ZeroPadding.pad (reserveOf 𝒞 vdS ((𝒞).enc i)) (encInOf 𝒞 b vdS 0 i) = A' ((𝒞).enc i).castSucc := by
    intro hN i hs
    have hm : 0 < (monomials coordC ph ci).length := lt_of_lt_of_eq hN (TraceData.hlen coordC ph ci sources L tgtC modeC)
    have h5 : i.val ≠ 5 := by
      intro h
      obtain ⟨i', hi'⟩ := enc5_slot mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph)
      exact hs i' (hi'.trans (congrArg (𝒞).enc (Fin.ext h.symm)))
    have hrsv : reserveOf 𝒞 vdS ((𝒞).enc i) = Rc := if_pos (hencP_R mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph) i).1
    rw [hrsv]
    have coef0 : (vdS).coefficient 0 = CloseoutFinalC10SupplierCalls.coefficientEstimate ((monomials coordC ph ci)[0]).coefficient := by
      show CloseoutFinalC10SupplierCalls.coefficientEstimate (((TraceData.order coordC ph ci).map (fun m => m.coefficient)).getD 0 0) = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hm]
      rfl
    have en0 : CloseoutRowsEstimatorCoefficients.Stream.Entry := ⟨(vdS).coefficient 0, (vdS).total 0, (vdS).denominator 0⟩
    rcases (by omega : i.val < 3 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10) with
      h | h | h | h | h | h | h | h
    · have enc012 : encInOf 𝒞 b vdS 0 i = RepairOrdinary.frame (CloseoutRowsEstimatorCoefficients.Stream.recordFields b
          (CloseoutFinalC10SupplierCalls.coefficientEstimate ((monomials coordC ph ci)[0]).coefficient) 0 0 ⟨i.val, by omega⟩) := by
        have hb := ebank_field b ⟨(vdS).coefficient 0, (vdS).total 0, (vdS).denominator 0⟩ ((vdS).D 0) ((vdS).cap 0) ((vdS).old 0) ⟨i.val, by omega⟩
        refine hb.trans ?_
        refine congrArg RepairOrdinary.frame ?_
        rw [coef0]
        exact recordFields_coef b _ _ _ ⟨i.val, h⟩
      rw [enc_lo mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph) i (by omega), enc012]
      exact (fenc012 hm ⟨i.val, h⟩).symm
    · have ei : i = 3 := Fin.ext h
      subst ei
      have eT : ((𝒞).enc 3).castSucc = Dims.encT (d := 𝔇) 𝒽1 3 := enc_lo mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph) 3 (by decide)
      rw [eT, fencK 3 (Or.inl rfl), (eE ⟨(vdS).coefficient 0, (vdS).total 0, (vdS).denominator 0⟩ ((vdS).old 0)).1]
      rfl
    · have ei : i = 4 := Fin.ext h
      subst ei
      have eT : ((𝒞).enc 4).castSucc = Dims.encT (d := 𝔇) 𝒽1 4 := enc_lo mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph) 4 (by decide)
      rw [eT, fenc4]
      show ZeroPadding.pad Rc (RepairOrdinary.frame (SignedSortKey.binary b ((vdS).denominator 0))) = _
      rw [show (vdS).denominator 0 = (TraceData.fractionOf coordC ph ci sources L tgtC modeC 0).2 from rfl,
        SourceBudget.denominator_at sources coordC ph ci L tgtC modeC 0]
    · have ei : i = 6 := Fin.ext h
      subst ei
      have eT : ((𝒞).enc 6).castSucc = Dims.encT (d := 𝔇) 𝒽1 5 := enc_hi mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph) 6 (by decide)
      rw [eT, fencK 5 (Or.inr (by decide)), hpay]
      rfl
    · have ei : i = 7 := Fin.ext h
      subst ei
      have eT : ((𝒞).enc 7).castSucc = Dims.encT (d := 𝔇) 𝒽1 6 := enc_hi mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph) 7 (by decide)
      rw [eT, fencK 6 (Or.inr (by decide)), (eE ⟨(vdS).coefficient 0, (vdS).total 0, (vdS).denominator 0⟩ ((vdS).old 0)).2.1]
      rfl
    · have ei : i = 8 := Fin.ext h
      subst ei
      have eT : ((𝒞).enc 8).castSucc = Dims.encT (d := 𝔇) 𝒽1 7 := enc_hi mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph) 8 (by decide)
      rw [eT, fencK 7 (Or.inr (by decide)), (eE ⟨(vdS).coefficient 0, (vdS).total 0, (vdS).denominator 0⟩ ((vdS).old 0)).2.2.1]
      rfl
    · have ei : i = 9 := Fin.ext h
      subst ei
      have eT : ((𝒞).enc 9).castSucc = Dims.encT (d := 𝔇) 𝒽1 8 := enc_hi mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph) 9 (by decide)
      rw [eT, fencK 8 (Or.inr (by decide)), (eE ⟨(vdS).coefficient 0, (vdS).total 0, (vdS).denominator 0⟩ ((vdS).old 0)).2.2.2.1]
      rfl
    · have ei : i = 10 := Fin.ext h
      subst ei
      have eT : ((𝒞).enc 10).castSucc = Dims.encT (d := 𝔇) 𝒽1 9 := enc_hi mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph) 10 (by decide)
      rw [eT, fencK 9 (Or.inr (by decide)), (eE ⟨(vdS).coefficient 0, (vdS).total 0, (vdS).denominator 0⟩ ((vdS).old 0)).2.2.2.2]
      rfl
  have hA0' : 0 < (vdS).entries.length → ∀ i, (∀ i', (𝒞).slots i' ≠ (𝒞).app i) → (∀ i', (𝒞).enc i' ≠ (𝒞).app i) →
      ZeroPadding.pad (reserveOf 𝒞 vdS ((𝒞).app i)) (appInOf 𝒞 b vdS 0 i) = A' ((𝒞).app i).castSucc := by
    intro hN i hs he
    rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5) with h | h | h | h | h | h
    · have ei : i = 0 := Fin.ext h
      subst ei
      exact absurd (enc6_app0 mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph)) (he 6)
    · have ei : i = 1 := Fin.ext h
      subst ei
      have hv := app1_wd mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph)
      have hw := wd_val mask packets rows sources res p k r ph 81 (by decide) (by decide)
      have hlt := wordSlot_lt sources p k r (scratchOf mask packets rows sources res) ph 81
      have ho := offset_ge_300 sources p k r
      have hF : ((𝒞).app 1).val < (𝔇).F := by rw [hv]; exact hlt
      have hrsv : reserveOf 𝒞 vdS ((𝒞).app 1) = 0 := if_neg (by rw [hv]; omega)
      have hx1 : ((𝒞).app 1).castSucc.val = ((𝒞).app 1).val := Fin.val_castSucc _
      have hfree := free_below e.ext2.ext1.ext 𝒽1 ((𝒞).app 1).castSucc (by rw [hx1, hv]; omega) (by rw [hx1, hv]; omega)
        (by rw [hx1]; exact hF)
      obtain ⟨-, a1⟩ := ffr ((𝒞).app 1).castSucc (by rw [hx1]; exact hF) hfree
        (hc15 _ (fun j => by rw [hx1]; exact hWnc 1 hF j))
        (fun he' => by have := congrArg Fin.val he'; rw [hx1, hq284, hv] at this; omega)
      obtain ⟨a2, -⟩ := hlowG ((𝒞).app 1).castSucc (by rw [hx1]; exact hF) (by rw [hx1, hv]; omega)
      rw [hrsv, pad_zero, a1, a2, hQ81]
      show CloseoutFinalC10AppendPositioning.tapes b (InitRun.D0 b) (CloseoutFinalC10AppendWorkspaceInit.capacity b)
        (CloseoutFinalC10AppendWorkspaceInit.capacity b) _ ((vdS).phasePrefix ++ (vdS).entries.take 0) 1 = _
      rw [List.take_zero, List.append_nil]
      rfl
    · have ei : i = 2 := Fin.ext h
      subst ei
      have eT : ((𝒞).app 2).castSucc = Dims.encT (d := 𝔇) 𝒽1 10 := app2_encT mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph)
      have hv : ((𝒞).app 2).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 + r_tapes (printerOf sources) + 10 := by
        have := congrArg Fin.val eT
        rw [Fin.val_castSucc, encT1_val] at this
        exact this
      have hrsv : reserveOf 𝒞 vdS ((𝒞).app 2) = Rc := if_pos (by rw [hv]; omega)
      rw [hrsv, eT, fencK 10 (Or.inr (by decide)),
        (eA ⟨(vdS).coefficient 0, (vdS).total 0, (vdS).denominator 0⟩ ((vdS).phasePrefix ++ (vdS).entries.take 0)).1]
      rfl
    · have ei : i = 3 := Fin.ext h
      subst ei
      have hv := app3_wd mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph)
      have hw := wd_val mask packets rows sources res p k r ph 90 (by decide) (by decide)
      have hlt := wordSlot_lt sources p k r (scratchOf mask packets rows sources res) ph 90
      have ho := offset_ge_300 sources p k r
      have hF : ((𝒞).app 3).val < (𝔇).F := by rw [hv]; exact hlt
      have hrsv : reserveOf 𝒞 vdS ((𝒞).app 3) = 0 := if_neg (by rw [hv]; omega)
      have hx1 : ((𝒞).app 3).castSucc.val = ((𝒞).app 3).val := Fin.val_castSucc _
      have hfree := free_below e.ext2.ext1.ext 𝒽1 ((𝒞).app 3).castSucc (by rw [hx1, hv]; omega) (by rw [hx1, hv]; omega)
        (by rw [hx1]; exact hF)
      obtain ⟨-, a1⟩ := ffr ((𝒞).app 3).castSucc (by rw [hx1]; exact hF) hfree
        (hc15 _ (fun j => by rw [hx1]; exact hWnc 3 hF j))
        (fun he' => by have := congrArg Fin.val he'; rw [hx1, hq284, hv] at this; omega)
      obtain ⟨a2, -⟩ := hlowG ((𝒞).app 3).castSucc (by rw [hx1]; exact hF) (by rw [hx1, hv]; omega)
      rw [hrsv, pad_zero, a1, a2, hQ90]
      show CloseoutFinalC10AppendPositioning.tapes b (InitRun.D0 b) (CloseoutFinalC10AppendWorkspaceInit.capacity b)
        (CloseoutFinalC10AppendWorkspaceInit.capacity b) _ ((vdS).phasePrefix ++ (vdS).entries.take 0) 3 = _
      rw [List.take_zero, List.append_nil]
      rfl
    · have ei : i = 4 := Fin.ext h
      subst ei
      have eT : ((𝒞).app 4).castSucc = Dims.encT (d := 𝔇) 𝒽1 11 := app4_encT mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph)
      have hv : ((𝒞).app 4).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 + r_tapes (printerOf sources) + 11 := by
        have := congrArg Fin.val eT
        rw [Fin.val_castSucc, encT1_val] at this
        exact this
      have hrsv : reserveOf 𝒞 vdS ((𝒞).app 4) = Rc := if_pos (by rw [hv]; omega)
      rw [hrsv, eT, fencK 11 (Or.inr (by decide)),
        (eA ⟨(vdS).coefficient 0, (vdS).total 0, (vdS).denominator 0⟩ ((vdS).phasePrefix ++ (vdS).entries.take 0)).2.1]
      rfl
    · have ei : i = 5 := Fin.ext h
      subst ei
      have eT : ((𝒞).app 5).castSucc = Dims.encT (d := 𝔇) 𝒽1 12 := app5_encT mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph)
      have hv : ((𝒞).app 5).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 + r_tapes (printerOf sources) + 12 := by
        have := congrArg Fin.val eT
        rw [Fin.val_castSucc, encT1_val] at this
        exact this
      have hrsv : reserveOf 𝒞 vdS ((𝒞).app 5) = Rc := if_pos (by rw [hv]; omega)
      rw [hrsv, eT, fencK 12 (Or.inr (by decide)),
        (eA ⟨(vdS).coefficient 0, (vdS).total 0, (vdS).denominator 0⟩ ((vdS).phasePrefix ++ (vdS).entries.take 0)).2.2]
      rfl
  have p2 := first_startV mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph) e
    coordC ci L tgtC modeC Rc Rk b layA factsA K K0 KH0 K1 K01 KH01 b vMB vMS Rc Rc Rc Rc vWS vRW vBF vU0 (vdS) hds0 (List.length_map _)
    rfl rfl rfl (rw_init sources selector coordC ph ci L tgtC modeC lay hlay hL1 hu 0) rfl hcR (TraceData.hlen coordC ph ci sources L tgtC modeC)
    hKpos hK hK0 H' A' cnt hcnt fnatH fnatA fcA fcH fInv flong (vdS).entries.length
    (fun i => hencP_R mask packets rows sources res hres p k r ph _ _ i) (fun i => happP_R mask packets rows sources res hres p k r ph _ _ i)
    hencInj happInj hKapp hE0 hA0'
  exact ⟨p1, p2.1, p2.2.1, p2.2.2.1, p2.2.2.2.1, p2.2.2.2.2, p3, p4, p5⟩

end start

end
end NearCubicWires.SourceSkeleton.StartB
end


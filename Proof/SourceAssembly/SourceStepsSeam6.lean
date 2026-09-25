import Proof.SourceAssembly.SourceClauseChain6
import Proof.SourceAssembly.SourceStepsSeam5

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

section seam5
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources)
  (res : Nat) (hres : 19 ≤ res) {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

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
local notation "vdC" => clauseVals mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt Dw capw logw resetw (oldAt coordC ph ci sources L tgtC modeC b Dw) Hd Ad Rc familyCost refillCost firstCost counterReserve

set_option hygiene false in
local notation "vdX" => clauseVals mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve

theorem seam6_clause (ph : Phase)
    (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) (PacketsGlue.RequestMeta.seedCount (decompositionOf sources)))
    (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources))) {gW : Nat}
    (e : (𝔇).RestExt3 se.extra sp.extra gW)
    (g7F : Phase → Σ s, Machine (UOf mask packets rows sources res p k r) s) (g7cost : Nat → Nat)
    (preFF : Phase → Σ s, Machine (UOf mask packets rows sources res p k r + 1) s)
    (compiler : Packets.CompilerLaws) (den : Nat) (hden : 0 < den) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)) states)
    (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (L : Nat) (Rc Rk b : Nat)
    (lay : TraceData.LayoutFamily coordC ph ci sources L tgtC modeC selector)
    (capsAt : Nat → RowCaps)
    (goodAt : ∀ m : Nat, RowCaps.Good selector (decompositionOf sources) (printerOf sources)
      (requestAt coordC ph ci L tgtC modeC m) (layA m) (factsA m) (capsAt m))    (K : Fin (UOf mask packets rows sources res p k r) → Prop)
    (K0 : Fin (UOf mask packets rows sources res p k r) → List Bool)
    (KH0 : Fin (UOf mask packets rows sources res p k r) → Nat)
    (hG7 : ResidentRunH (g7F ph).2 g7cost mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
      ((𝔇).maskSlots 𝒽) ((𝔇).pslots 𝒽) ((𝔇).slot 𝒽) ((𝔇).ret 𝒽) ((𝔇).scr 𝒽 0) ((𝔇).scr 𝒽 1)
      ((𝔇).familySlots 𝒽) ((𝔇).poolSlots 𝒽) (Dims.rewind2Slots e.ext2.ext1.ext 𝒽)
      ((𝔇).scr 𝒽 5) ((𝔇).scr 𝒽 6) ((𝔇).scr 𝒽 7) ((𝔇).scr 𝒽 8) ((𝔇).scr 𝒽 9) ((𝔇).scr 𝒽 10)
      (Dims.lenTape e.ext2.ext1.ext 𝒽) coordC ph ci L tgtC modeC Rc b
      ((𝔇).pcT e.ext2.ext1 𝒽 ⟨70, by unfold restPc; omega⟩)
      (fun i => (𝔇).pcT e.ext2.ext1 𝒽 ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩) layA capsAt
      (Dims.Rpad (d := 𝔇) (eX := se.extra) (pX := sp.extra) (gW := gW) (V := UOf mask packets rows sources res p k r) Rc)
      (RestIn4 (𝔇) se.extra sp.extra gW Rc ((𝔇).pcT e.ext2.ext1 𝒽 ⟨64, by unfold restPc; omega⟩) K K0 KH0)
      (fun x => OutV (𝔇) se.extra sp.extra gW x.val))
    (V : Nat) (dflt : P1TopDownPaidReusable.Datum) (Dw capw logw resetw : Nat)
    (Hd : Nat → Fin (UOf mask packets rows sources res p k r) → Nat) (Ad : Nat → Fin (UOf mask packets rows sources res p k r) → List Bool)
    (old : Nat → List Bool) (hold : ∀ j, old (j+1) = oldAt coordC ph ci sources L tgtC modeC b Dw (j+1))
    (familyCost firstCost counterReserve : Nat)
    (cW cQ cB cS refillCost N : Nat)
    -- the admission layout carries the uniform degree (`hrw`)
    (hlay : ∀ j, (lay j).degree = Admission.uniformDeg vQ L) (hL1 : 1 ≤ L)
    (hu : 1 ≤ vQ / (200 * (normalizedLiveCount vQ L + 1 + 1)))
    -- the code's `enc`/`app` placement
    -- constants
    (hRk : Rc ≤ Rk) (hcW : Rc ≤ cW) (hcQ : Rc ≤ cQ) (hcB : Rc ≤ cB) (hcS : Rc ≤ cS)
    (hSl : vWS + 2 ≤ Rc) (hRl : vRW + 2 ≤ Rc) (hBl : vBF + 2 ≤ Rc) (h4b : 4*b+5 ≤ Rc) (hUl : vU0 ≤ Rc)
    (hMb : vMB ≤ Rc) (hMs : vMS ≤ Rc)
    (hKpos : ∀ x, K x → x.val < (𝔇).F ∨
      ((𝔇).B + 29 + restPc se.extra sp.extra gW ≤ x.val ∧ x ≠ Dims.hrT e 𝒽 10 ∧ x ≠ Dims.hrT e 𝒽 11))
    (hKpad : ∀ x, K x → (𝔇).F ≤ x.val → ZeroPadding.pad Rc (K0 x) = K0 x)
    (hKapp : ∀ x, K x → ∀ i, (𝒞).app i ≠ x)
    (hKfree : ∀ x, K x → Cycle.Free ((𝔇).slot 𝒽) ((𝔇).maskSlots 𝒽) ((𝔇).pslots 𝒽) ((𝔇).poolSlots 𝒽)
      ((𝔇).familySlots 𝒽) (Dims.rewind2Slots e.ext2.ext1.ext 𝒽) x ∨
      x = Dims.rewind2Slots e.ext2.ext1.ext 𝒽 1 ∨ x = Dims.rewind2Slots e.ext2.ext1.ext 𝒽 2)
    (hKr1 : ∀ j, j < N → K (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 1) →
      K0 (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 1) = List.replicate (capsAt (j+1)).descriptorReserve true ∧
      KH0 (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 1) = 0)
    (hKr2 : ∀ j, j < N → K (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 2) →
      K0 (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 2) = List.replicate (capsAt (j+1)).descriptorReserve false ∧
      KH0 (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 2) = 0)
    -- per call `j < N`
    (hj : ∀ j, j < N → j + 1 ≤ (monomials coordC ph ci).length)
    (hRc : ∀ j, j < N → j + 1 + 3 ≤ Rc)
    (hlog : ∀ j, j < N → 2 * ((requestAt coordC ph ci L tgtC modeC (j+1)).input (decompositionOf sources)).length + 1 ≤ Rc)
    (he1 : ∀ j, j < N → 1 ≤ PacketsGlue.RequestMeta.seedCount (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1)))
    (hpw : ∀ j, j < N → (CloseoutRowsCountBinary.bits (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1)))).length ≤ b)
    (hfirst : ∀ j, j < N → PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1)) * 2^(natBitLength (PacketsGlue.RequestMeta.seedCount (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1)))) < 2^b)
    (hsecond : ∀ j, j < N → PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1)) * PacketsGlue.RequestMeta.seedCount (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1)) * 2^(vQ+1) < 2^b)
    (hdescR : ∀ j, j < N → (capsAt (j+1)).descriptorReserve ≤ Rc)
    (hL : ∀ j, j < N → (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length + 3 ≤ Rc)
    (hfamH : ∀ j, j < N → ∀ i, r_inputH (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1))) (layA (j+1)) (factsA (j+1))) vWS vRW vBF (dataList (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1))) (layA (j+1)) (factsA (j+1))).length i + (fuelOf 𝒞 b vdX (j+1)) + 1 ≤ Rc)
    (hwinI : ∀ j, j < N → cursorCost j + 1 + g7cost (j+1) + 1 + (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordC ph ci L tgtC modeC (j+1)) (layA (j+1)) (factsA (j+1)) (capsAt (j+1)) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length then vMB else vMS) vU0 vWS vRW vBF b (0)) + 1 ≤ Rc)
    (hwinZ : ∀ j, j < N → (restCost se sp g7cost (requestAt coordC ph ci L tgtC modeC (j+1)) Rc b vQ (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length vMB vMS j) + 1 + (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordC ph ci L tgtC modeC (j+1)) (layA (j+1)) (factsA (j+1)) (capsAt (j+1)) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length then vMB else vMS) vU0 vWS vRW vBF b (0)) + 1 ≤ Rk)
    (hcost : ∀ j, j < N → (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordC ph ci L tgtC modeC (j+1)) (layA (j+1)) (factsA (j+1)) (capsAt (j+1)) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length then vMB else vMS) vU0 vWS vRW vBF b ((4*Rk+7) + 1 + ((4*Rc+7) + 1 + ((restCost se sp g7cost (requestAt coordC ph ci L tgtC modeC (j+1)) Rc b vQ (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length vMB vMS j) + 1 + refreshCost Rc)))) ≤ refillCost)
    -- the clause bridge's data: the chain start, the code's `app` tapes
    (H0c : Fin (UOf mask packets rows sources res p k r) → Nat)
    (A0c : Fin (UOf mask packets rows sources res p k r) → List Bool) :
    SeamSpec N (fun _ => 0) (𝒞).slots (inTOf 𝒞 b vdX)
      (fun j H A => Rest.InvR e 𝒽 Rc Rk K K0 KH0 j b vQ vMB vMS cW cQ cB cS vWS vRW vBF b vU0 (fuelOf 𝒞 b vdX j) H A ∧
        (∀ x : Fin (UOf mask packets rows sources res p k r), x.val < (𝔇).F →
          Cycle.Free ((𝔇).slot 𝒽) ((𝔇).maskSlots 𝒽) ((𝔇).pslots 𝒽) ((𝔇).poolSlots 𝒽) ((𝔇).familySlots 𝒽)
            (Dims.rewind2Slots e.ext2.ext1.ext 𝒽) x →
          (∀ i, (𝒞).app i ≠ x) → A x = A0c x ∧ H x = H0c x) ∧
        (∀ i, ((𝒞).app i).val < (𝔇).F → H ((𝒞).app i) = H0c ((𝒞).app i) ∧
          (0 < j → A ((𝒞).app i) = appTOf b vdX (j-1) i)) ∧
        (∀ kk : Fin 13, H (Dims.encT (d := 𝔇) 𝒽 kk) = H0c (Dims.encT (d := 𝔇) 𝒽 kk)) ∧
        (j < N → (∀ i, (∀ i', (𝒞).slots i' ≠ (𝒞).enc i) → A ((𝒞).enc i) = encInOf 𝒞 b vdX j i) ∧
          (∀ i, (∀ i', (𝒞).slots i' ≠ (𝒞).app i) → (∀ i', (𝒞).enc i' ≠ (𝒞).app i) → A ((𝒞).app i) = appInOf 𝒞 b vdX j i)) ∧
        (N ≤ j → 0 < j → ∀ kk : Fin 13, (kk.val = 3 ∨ 5 ≤ kk.val) →
          A (Dims.encT (d := 𝔇) 𝒽 kk) = ZeroPadding.pad Rc
            (install (𝒞).app (install (𝒞).enc (fun _ => []) (encWOf b vdX (j-1))) (appTOf b vdX (j-1)) (Dims.encT (d := 𝔇) 𝒽 kk))) ∧
        (N ≤ j → 0 < j → ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → (A (Dims.encT (d := 𝔇) 𝒽 kk)).length ≤ Rc))
      (goodOf 𝒞 b vdX) := by
  have hvl : b + 2 ≤ Rc := by omega
  have hw2 : 2 * b + 1 ≤ Rc := by omega
  have hlenE : (vdX).entries.length = (monomials coordC ph ci).length := TraceData.hlen coordC ph ci sources L tgtC modeC
  have hX : ∀ j (i : Fin 11), encInOf 𝒞 b vdX (j+1) i = encInOf 𝒞 b vdC (j+1) i := fun j i => by
    show e_bank _ _ _ _ (old (j+1)) i = e_bank _ _ _ _ (oldAt coordC ph ci sources L tgtC modeC b Dw (j+1)) i
    rw [hold]
    rfl
  exact Bridge.seam5W_spec mask packets rows sources res hres p k r ph se sp e (g7F ph).2 g7cost (preFF ph) coordC ci L tgtC modeC Rc Rk b
    layA capsAt factsA goodAt K K0 KH0 hG7 vdX b cW cQ vMB vMS cB cS vWS vRW vBF vU0 refillCost N
    (fun i => hencP_R mask packets rows sources res hres p k r ph _ _ i)
    (fun i => happP_R mask packets rows sources res hres p k r ph _ _ i)
    (hds_clause mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L lay
      (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve)
    (hxs_clause mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L lay
      (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (hrw_clause mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L lay
      V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve hlay hL1 hu)
    rfl rfl
    hRk hcW hcQ hcB hcS hSl hRl hBl hvl hw2 hUl hMb hMs hKpos hKpad hKapp hKfree hKr1 hKr2 hj hRc
    (henc0_of mask packets rows sources res hres p k r ph _ _ vdX b Rc N h4b)
    hlog he1 hpw hfirst hsecond hdescR hL hfamH hwinI hwinZ hcost H0c A0c
    (app_injective_R mask packets rows sources res hres p k r ph _ _)
    (enc_injective_R mask packets rows sources res hres p k r ph _ _)
    (hcovE_R mask packets rows sources res hres p k r ph _ _)
    (hcov_R mask packets rows sources res hres p k r ph _ _)
    (app_free_R mask packets rows sources res hres p k r ph _ _ e.ext2.ext1.ext)
    -- hvCoef
    (fun j _ hm i kk hk => by
      rw [hX]
      have hi := enc_idx mask packets rows sources res hres p k r ph _ _ i ⟨kk.val, by omega⟩ (by show kk.val < 5; omega) hk
      have hie : i = ⟨kk.val, by have := kk.isLt; omega⟩ := Fin.ext hi
      rw [hie]
      exact encIn_coef mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site
        codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt b Dw capw logw resetw Hd Ad Rc familyCost refillCost
        firstCost counterReserve j hm kk)
    -- hvDen
    (fun j _ i hk => by
      rw [hX]
      have hi := enc_idx mask packets rows sources res hres p k r ph _ _ i 4 (by decide) hk
      have hie : i = 4 := Fin.ext hi
      subst hie
      exact encIn_den mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site
        codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt b Dw capw logw resetw Hd Ad Rc familyCost refillCost
        firstCost counterReserve j)
    -- hvEnc
    (fun j _ i hs ha hne => by
      rw [hX]
      have h5 : i.val ≠ 5 := by
        intro h
        have hie : i = 5 := Fin.ext h
        subst hie
        obtain ⟨i', hi'⟩ := enc5_slot mask packets rows sources res hres p k r ph _ _
        exact hs i' hi'
      have h6 : i.val ≠ 6 := by
        intro h
        have hie : i = 6 := Fin.ext h
        subst hie
        exact ha 0 (enc6_app0 mask packets rows sources res hres p k r ph _ _).symm
      have h04 : ¬ (i.val < 3 ∨ i.val = 4) := by
        intro h
        exact hne ⟨i.val, by have := i.isLt; omega⟩ (by simpa using h)
          (enc_eq_encT mask packets rows sources res hres p k r ph _ _ ⟨i.val, by have := i.isLt; omega⟩ (by show i.val < 5; omega))
      exact encIn_keep mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site
        codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt b Dw capw logw resetw Hd Ad Rc familyCost refillCost
        firstCost counterReserve j i (by have := i.isLt; omega))
    -- hvEA
    (fun j _ i i' h _ => by
      rw [hX]
      obtain ⟨h6, h0⟩ := app_enc_idx mask packets rows sources res hres p k r ph _ _ i i' h
      have hie : i = 6 := Fin.ext h6
      have hie' : i' = 0 := Fin.ext h0
      subst hie hie'
      exact encIn_payload mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site
        codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt b Dw capw logw resetw Hd Ad Rc familyCost refillCost
        firstCost counterReserve j)
    -- hvApp
    (fun j hlt i _ he => by
      have hjl : j < (vdX).entries.length := by have := hj (j+1) hlt; omega
      refine appIn_keep mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site
        codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt b Dw capw logw resetw Hd Ad Rc familyCost refillCost
        firstCost counterReserve j hjl i (fun h0 => ?_)
      have hie : i = 0 := Fin.ext h0
      subst hie
      exact he 6 (enc6_app0 mask packets rows sources res hres p k r ph _ _))

end seam5

end
end NearCubicWires.SourceSteps
end

import Proof.Packets.SrcLayRows
import Proof.SourceAssembly.SourceSkelCaps

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

namespace NearCubicWires.SourceStart.YSite
noncomputable section

section lay
variable (sources : EightSources) (selector : CyclicChoice.Laws)
  {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
  (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
  (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits)) (L target : Nat)

theorem layoutAtOf_w (mode : Bool) (lay : TraceData.LayoutFamily coordinate ph ci sources L target mode selector) (m : Nat) :
    (SourceSkeleton.layoutAtOf sources selector coordinate ph ci L target mode lay m).w = (lay m).w := by
  cases mode <;> rfl

theorem layoutAtOf_degree (mode : Bool) (lay : TraceData.LayoutFamily coordinate ph ci sources L target mode selector) (m : Nat) :
    (SourceSkeleton.layoutAtOf sources selector coordinate ph ci L target mode lay m).degree = (lay m).degree := by
  cases mode <;> rfl

theorem layoutAtOf_C (mode : Bool) (lay : TraceData.LayoutFamily coordinate ph ci sources L target mode selector) (m : Nat) :
    (SourceSkeleton.layoutAtOf sources selector coordinate ph ci L target mode lay m).C = (lay m).C := by
  cases mode <;> rfl

end lay

section siteadm
variable (selector : CyclicChoice.Laws) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

theorem small_adm (xtra : NearCubicWires.SourceSkeleton.Fill.XtraW selector) (n : ℕ)
    (hext : ParamsV4.extraW selector xtra mask packets rows sources gamma hg hh p ≤ n) :
    ParamsV4.smallDen0W selector mask packets rows sources gamma hg hh p ≤
        (ParamsV4.fPW selector xtra mask packets rows).capIndex sources gamma hg hh p + 1 ∧
      ParamsV4.smallOnsetW selector mask packets rows sources gamma hg hh p ≤
        C10PartsSchedule.widthAt sources (FirstW.kSite selector xtra mask packets rows sources gamma hg hh p) n :=
  ⟨le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (SourceBudget.den0_le (ParamsV4.den0W selector mask packets rows) sources gamma hg hh p),
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (ParamsV4.qOnW_le_width selector mask packets rows xtra sources gamma hg hh p n hext)⟩

end siteadm

end
end NearCubicWires.SourceStart.YSite

namespace NearCubicWires.SourceStart.YSite
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

section y1
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

set_option hygiene false in
local notation "𝔏𝔖" => ClassV4.siteL4 selector mask packets rows sources gamma hg hh p

theorem y1_site (hg : 0 < gamma) (hh : gamma < 1/2) (compiler : Packets.CompilerLaws) (den : Nat) (hden : 0 < den) (n : Nat)
    (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (ph : Phase) (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)))
    (L : Nat) (lay : TraceData.LayoutFamily coordC ph ci sources L tgtC modeC selector) (capsAt : Nat → RowCaps) (V b N : Nat)
    (hLe : L = 𝔏𝔖) (hVe : V = SourceBudget.Params.VvOf selector sources p L (C10PartsSchedule.widthAt sources k n))
    (hbe : b = C10PartsSchedule.entryWidthSchedule sources k r n) (hr : r = SourceSteps.rBsel sources p)
    (hcapsE : ∀ m, capsAt m = SourceSkeleton.capsU (SourceBudget.Pow2.hFOf2 selector sources p L (C10PartsSchedule.widthAt sources k n)) (SourceBudget.Pow2.cCOf2 selector sources p L (C10PartsSchedule.widthAt sources k n))
      (SourceBudget.Params.VvOf selector sources p L (C10PartsSchedule.widthAt sources k n)) (SourceBudget.Pow2.rROf2 selector sources p packets (C10PartsSchedule.widthAt sources k n)))
    (hlayW : ∀ m, (lay m).w ≤ vQ) (hlayD : ∀ m, (lay m).degree = Admission.uniformDeg vQ L)
    (hlayC : ∀ m, (lay m).C = SourceBudget.Params.COf selector sources p (C10PartsSchedule.widthAt sources k n))
    (hcut : CloseoutWitnessPolicy.inputCutoff sources ≤ n) (h201 : 201 * normalizedLiveCount (C10PartsSchedule.widthAt sources k n) L ≤ (C10PartsSchedule.widthAt sources k n))
    (hsd : ParamsV4.smallDen0W selector mask packets rows sources gamma hg hh p ≤ den)
    (hso : ParamsV4.smallOnsetW selector mask packets rows sources gamma hg hh p ≤ (C10PartsSchedule.widthAt sources k n))
    (hNb : N ≤ b) :
    ∀ j, j < N →
      ((ClassV4.siteY4 selector mask packets rows).at sources gamma hg hh p 𝔏𝔖 k).In 4 𝔏𝔖 n (C10PartsSchedule.widthAt sources k n)
        (Rest.restCost (SourceBudget.seOf sources) (SourceBudget.spOf sources) (fun _ => 0) (requestAt coordC ph ci L tgtC modeC (j+1)) 0 b vQ (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length vMB vMS j +
          Rest.cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordC ph ci L tgtC modeC (j+1)) (layA (j+1))
            (factsA (j+1)) (capsAt (j+1)) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length then vMB else vMS) vU0 vWS vRW vBF b 0) := by
  intro j hj
  obtain ⟨hadm, hq, hL⟩ := SourceSteps.site_call_facts sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp ph ci
    L hden hcut (j+1)
  have hvq : vQ = (C10PartsSchedule.widthAt sources k n) := Admission.req_arity sources k (PolynomialClock.ordinaryClock k) x _ hcut
  have hLs : (requestAt coordC ph ci L tgtC modeC (j+1)).liveScale = 𝔏𝔖 := hL.trans hLe
  -- the layout at call j+1
  have hlw : (layA (j+1)).w ≤ (requestAt coordC ph ci L tgtC modeC (j+1)).q := by
    rw [layoutAtOf_w, hq, ← hvq]; exact hlayW (j+1)
  have hld : (layA (j+1)).degree ≤ (requestAt coordC ph ci L tgtC modeC (j+1)).q := by
    rw [layoutAtOf_degree, hlayD, hq, ← hvq]; exact Admission.uniformDeg_le _ _
  have hlC0 : (layA (j+1)).C = SourceBudget.Params.COf selector sources p (requestAt coordC ph ci L tgtC modeC (j+1)).q := by
    rw [layoutAtOf_C, hlayC, hq]
  have hK : normalizedLiveCount (requestAt coordC ph ci L tgtC modeC (j+1)).q (requestAt coordC ph ci L tgtC modeC (j+1)).liveScale + (requestAt coordC ph ci L tgtC modeC (j+1)).q / 4 ≤ (requestAt coordC ph ci L tgtC modeC (j+1)).q := by
    rw [hq, hL]; omega
  have hcf := NearCubicWires.SourceStart.Meta.capsFit3 selector sources p den hden _ hadm (layA (j+1)) hld hlC0 hK
  have hcf2 := hcf.2.1
  have hcf3 := hcf.2.2.1
  have hcf4 := hcf.2.2.2.1
  rw [hq, hL] at hcf2 hcf3 hcf4
  -- the small size and the raw word
  have hsm : ((requestAt coordC ph ci L tgtC modeC (j+1)).smallSize (decompositionOf sources)) ^ (SourceBudget.DmOf packets rows SourceBudget.Params.degOf sources gamma hg hh p) ≤
      1 * RuntimeShape.smallClass 4 0 (requestAt coordC ph ci L tgtC modeC (j+1)).q :=
    Classical.choose_spec (Classical.choose_spec (Admission.small_poly selector (decompositionOf sources) p.clauseDegree
      (ParamsV4.TW sources gamma hg hh p) (ParamsV4.LW selector mask packets rows sources gamma hg hh p)
      (SourceBudget.DmOf packets rows SourceBudget.Params.degOf sources gamma hg hh p) 4
      (ParamsV4.one_le_LW selector mask packets rows sources gamma hg hh p) (by decide))) den hsd _ hadm hLs (hq ▸ hso)
  have hrows := SourceBudget.Params.rowsFit (decompositionOf sources) hden _ hadm
  have hsmP : ((requestAt coordC ph ci L tgtC modeC (j+1)).smallSize (decompositionOf sources)) ^ (packets (decompositionOf sources)).degree ≤
      1 * RuntimeShape.smallClass 4 0 (requestAt coordC ph ci L tgtC modeC (j+1)).q := by
    have hD := (SourceBudget.DmOf_spec packets rows SourceBudget.Params.degOf sources gamma hg hh p).1
    rcases Nat.eq_zero_or_pos ((requestAt coordC ph ci L tgtC modeC (j+1)).smallSize (decompositionOf sources)) with h0 | h0
    · rw [h0]
      have hc : 1 ≤ 1 * RuntimeShape.smallClass 4 0 (requestAt coordC ph ci L tgtC modeC (j+1)).q := by
        unfold RuntimeShape.smallClass
        have := Nat.one_le_two_pow (n := (requestAt coordC ph ci L tgtC modeC (j+1)).q / 4)
        simp only [pow_zero, one_mul]
        exact this
      rcases Nat.eq_zero_or_pos (packets (decompositionOf sources)).degree with e | e
      · rw [e, pow_zero]; exact hc
      · rw [zero_pow (by omega)]; exact Nat.zero_le _
    · exact (Nat.pow_le_pow_right h0 hD).trans hsm
  have hraw := SourceBudget.Pow2.rawFit2 selector sources p packets _ _ (SourceSteps.raw_length_le (packets (decompositionOf sources)) _) hrows hsmP
  rw [hq] at hraw
  have hgood : RowCaps.Good selector (decompositionOf sources) (printerOf sources) (requestAt coordC ph ci L tgtC modeC (j+1)) (layA (j+1)) (factsA (j+1)) (capsAt (j+1)) := by
    rw [hcapsE]
    exact SourceSkeleton.goodAt_uniform selector (decompositionOf sources) (printerOf sources) _ _ _ hcf.1 _ _ _ _ hcf2 hcf3
      hcf4 hraw
  -- the size facts
  have hin := SourceBudget.Params.inFit (decompositionOf sources) hden _ hadm 𝔏𝔖 hLs
  have hgs := SourceBudget.Params.gsFit (decompositionOf sources) hden _ hadm
  obtain ⟨hMs0, hMb0, hU00⟩ := SourceBudget.Params.scalarsFit L vQ
  have hrB : r ≤ SourceBudget.Params.rB sources gamma hg hh p := by rw [hr]; exact le_of_eq rfl
  have hbF := SourceBudget.Params.bFit sources hg hh p k r n hrB
  have hE0 : SourceBudget.Params.rB sources gamma hg hh p ≤ ClassV3.gEv3 selector mask packets rows sources gamma hg hh p := by
    have h1 : SourceBudget.Params.rB sources gamma hg hh p ≤ ClassV3.gE0v3 selector mask packets rows sources gamma hg hh p := by
      unfold ClassV3.gE0v3 SourceBudget.Params.gE0; omega
    have h2 : ClassV3.gE0v3 selector mask packets rows sources gamma hg hh p + 64 ≤
        (ClassV3.gE0v3 selector mask packets rows sources gamma hg hh p + 64) ^ 3 := Nat.le_self_pow (by decide) _
    show _ ≤ (ClassV3.gE0v3 selector mask packets rows sources gamma hg hh p + 64) ^ 3
    omega
  have hC0 : C10PartsSchedule.thresholdFloor sources + 1 ≤ ClassV3.gCv3 selector mask packets rows sources gamma hg hh p := by
    have h1 : C10PartsSchedule.thresholdFloor sources ≤ ClassV3.gC0v3 selector packets sources gamma hg hh p := by
      unfold ClassV3.gC0v3 SourceBudget.Params.gC0; omega
    have hpos : ClassV3.gEv3 selector mask packets rows sources gamma hg hh p ≠ 0 := by
      unfold ClassV3.gEv3; positivity
    have h2 : ClassV3.gC0v3 selector packets sources gamma hg hh p + 2 ≤
        (ClassV3.gC0v3 selector packets sources gamma hg hh p + 2) ^ ClassV3.gEv3 selector mask packets rows sources gamma hg hh p :=
      Nat.le_self_pow hpos _
    show _ ≤ (ClassV3.gC0v3 selector packets sources gamma hg hh p + 2) ^ ClassV3.gEv3 selector mask packets rows sources gamma hg hh p
    omega
  have hjj : j ≤ ClassV3.gCv3 selector mask packets rows sources gamma hg hh p * ((requestAt coordC ph ci L tgtC modeC (j+1)).q + 1) ^ ClassV3.gEv3 selector mask packets rows sources gamma hg hh p := by
    rw [hq]
    have hjb : j ≤ C10PartsSchedule.entryWidthSchedule sources k r n := by omega
    have hp1 : ((C10PartsSchedule.widthAt sources k n) + 1) ^ SourceBudget.Params.rB sources gamma hg hh p ≤ ((C10PartsSchedule.widthAt sources k n) + 1) ^ ClassV3.gEv3 selector mask packets rows sources gamma hg hh p :=
      Nat.pow_le_pow_right (by omega) hE0
    calc j ≤ C10PartsSchedule.entryWidthSchedule sources k r n := hjb
      _ ≤ (C10PartsSchedule.thresholdFloor sources + 1) * ((C10PartsSchedule.widthAt sources k n) + 1) ^ SourceBudget.Params.rB sources gamma hg hh p := hbF
      _ ≤ ClassV3.gCv3 selector mask packets rows sources gamma hg hh p * ((C10PartsSchedule.widthAt sources k n) + 1) ^ ClassV3.gEv3 selector mask packets rows sources gamma hg hh p :=
        Nat.mul_le_mul hC0 hp1
  have key := SourceBudget.yFam_site mask packets rows SourceBudget.Params.degOf SourceBudget.Params.tgOf (ClassV4.KFc4 selector mask packets rows)
    (ClassV4.siteL4 selector mask packets rows) (ClassV4.KFc4_free selector mask packets rows) sources gamma hg hh p k n den (requestAt coordC ph ci L tgtC modeC (j+1))
    (layA (j+1)) (factsA (j+1)) (capsAt (j+1)) (fun _ => 0) b vMB vMS vU0 V b j hq hLs hden hadm hin hrows hsm hlw hld
    (le_of_eq hlC0)
    (by rw [hcapsE, hq, hLe]; exact SourceBudget.Pow2.hFOf2_le selector sources p _ _)
    (by rw [hcapsE, hq, hLs, hLe]; exact SourceBudget.Pow2.cCOf2_le selector sources p _ _)
    (by rw [hcapsE, hq, hLs, hLe]; exact le_trans (le_of_eq rfl) (Nat.le_add_right _ _))
    (by rw [hcapsE, hq]; exact SourceBudget.Pow2.rROf2_le selector sources p packets _)
    hgood hgs
    (by rw [hq, ← hvq]; exact hMb0) (by rw [hq, ← hvq]; exact hMs0) (by rw [hq, ← hvq]; exact hU00)
    (by rw [hq, hbe]; exact hbF) (by rw [hq, hbe]; exact hbF) hjj
    (by rw [hVe, hq, hLs, hLe]; exact le_rfl) (Nat.zero_le _)
  have e : (requestAt coordC ph ci L tgtC modeC (j+1)).q = vQ := hq.trans hvq.symm
  have e2 : Rest.restCost (SourceBudget.seOf sources) (SourceBudget.spOf sources) (fun _ => 0) (requestAt coordC ph ci L tgtC modeC (j+1)) 0 b (requestAt coordC ph ci L tgtC modeC (j+1)).q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length vMB vMS j =
      Rest.restCost (SourceBudget.seOf sources) (SourceBudget.spOf sources) (fun _ => 0) (requestAt coordC ph ci L tgtC modeC (j+1)) 0 b vQ (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length vMB vMS j :=
    congrArg (fun t => Rest.restCost (SourceBudget.seOf sources) (SourceBudget.spOf sources) (fun _ => 0) (requestAt coordC ph ci L tgtC modeC (j+1)) 0 b t (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length vMB vMS j) e
  rw [e2] at key
  exact key

end y1

end
end NearCubicWires.SourceStart.YSite
end


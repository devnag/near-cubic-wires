import Proof.Packets.SrcYSite

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
attribute [local irreducible] P1TopDownPaidPayload.tapes

section y0
variable {selector : CyclicChoice.Laws} (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k r scratch : Nat)

set_option hygiene false in
local notation "oracleC" => C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits
set_option hygiene false in
local notation "coordC" => PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x oracleC bits
set_option hygiene false in
local notation "tgtC" => C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)
set_option hygiene false in
local notation "modeC" => PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp
set_option hygiene false in
local notation "vQ" => (req sources k (PolynomialClock.ordinaryClock k) x oracleC).arity
set_option hygiene false in
local notation "𝔏𝔖" => ClassV4.siteL4 selector mask packets rows sources gamma hg hh p

theorem y0_site (hg : 0 < gamma) (hh : gamma < 1/2) (den : Nat) (hden : 0 < den) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (ph : Phase) (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x oracleC)) (L : Nat)
    (layoutAt : ∀ m : Nat, Packets.Layout (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC m).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC m)))
    (factsAt : ∀ m : Nat, ∀ row ∈ ((requestAt coordC ph ci L tgtC modeC m).family (decompositionOf sources)).rows,
      Packets.PacketFacts (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC m).family (decompositionOf sources))
        (geometryOf selector (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC m)) row)
    (capsAt : Nat → RowCaps) (w q Mb Ms U0 S Rw B v C : Nat)
    (hLe : L = 𝔏𝔖) (hr : r = SourceSteps.rBsel sources p)
    (hwE : w = C10PartsSchedule.entryWidthSchedule sources k r n) (hvE : v = C10PartsSchedule.entryWidthSchedule sources k r n) (hqE : q = vQ)
    (hMbE : Mb = InitRun.Mb L vQ) (hMsE : Ms = InitPost.Ms L vQ) (hU0E : U0 = InitRun.U0 L vQ)
    (hSE : S = P1TopDownPaidReusableReserves.workspace (printerOf sources) (SourceBudget.Params.VvOf selector sources p L (C10PartsSchedule.widthAt sources k n)))
    (hRwE : Rw = P1TopDownPaidReusableReserves.rewind (printerOf sources) (SourceBudget.Params.VvOf selector sources p L (C10PartsSchedule.widthAt sources k n)))
    (hBE : B = P1TopDownPaidReusableReserves.buffer (SourceBudget.Params.VvOf selector sources p L (C10PartsSchedule.widthAt sources k n)))
    (hC0 : C ≤ PCPPQueryCachedBounds.capacity (CloseoutLanguage.selectedPCPP sources)
      ((req sources k (PolynomialClock.ordinaryClock k) x oracleC).circuit.size + (req sources k (PolynomialClock.ordinaryClock k) x oracleC).arity))
    (hcapsE : capsAt 0 = SourceSkeleton.capsU (SourceBudget.Pow2.hFOf2 selector sources p L (C10PartsSchedule.widthAt sources k n)) (SourceBudget.Pow2.cCOf2 selector sources p L (C10PartsSchedule.widthAt sources k n))
      (SourceBudget.Params.VvOf selector sources p L (C10PartsSchedule.widthAt sources k n)) (SourceBudget.Pow2.rROf2 selector sources p packets (C10PartsSchedule.widthAt sources k n)))
    (hlW : (layoutAt 0).w ≤ vQ) (hlD : (layoutAt 0).degree = Admission.uniformDeg vQ L)
    (hlC : (layoutAt 0).C = SourceBudget.Params.COf selector sources p (C10PartsSchedule.widthAt sources k n))
    (hcut : CloseoutWitnessPolicy.inputCutoff sources ≤ n) (h201 : 201 * normalizedLiveCount (C10PartsSchedule.widthAt sources k n) L ≤ (C10PartsSchedule.widthAt sources k n))
    (hsd : ParamsV4.smallDen0W selector mask packets rows sources gamma hg hh p ≤ den)
    (hso : ParamsV4.smallOnsetW selector mask packets rows sources gamma hg hh p ≤ (C10PartsSchedule.widthAt sources k n)) :
    ((ClassV4.siteYF04 selector mask packets rows).at sources gamma hg hh p 𝔏𝔖 k).In 4 𝔏𝔖 n (C10PartsSchedule.widthAt sources k n)
      (6 * C + 0 + Rest.backCost (SourceBudget.seOf sources) (SourceBudget.spOf sources) (requestAt coordC ph ci L tgtC modeC 0) 0 w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC 0).family (decompositionOf sources))).gs).length Mb Ms +
        Rest.cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordC ph ci L tgtC modeC 0) (layoutAt 0) (factsAt 0)
          (capsAt 0) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC 0).family (decompositionOf sources))).gs).length then Mb else Ms) U0 S Rw B v 0) := by
  subst hwE hvE hqE hMbE hMsE hU0E hSE hRwE hBE
  obtain ⟨hadm, hq, hL⟩ := SourceSteps.site_call_facts sources p den hden k r scratch n x bits hp ph ci L hden hcut 0
  have hvq : vQ = (C10PartsSchedule.widthAt sources k n) := Admission.req_arity sources k (PolynomialClock.ordinaryClock k) x _ hcut
  have hLs : (requestAt coordC ph ci L tgtC modeC 0).liveScale = 𝔏𝔖 := hL.trans hLe
  have e' : vQ = (requestAt coordC ph ci L tgtC modeC 0).q := hvq.trans hq.symm
  have hlw : (layoutAt 0).w ≤ (requestAt coordC ph ci L tgtC modeC 0).q := hlW.trans (le_of_eq e')
  have hld : (layoutAt 0).degree ≤ (requestAt coordC ph ci L tgtC modeC 0).q := (le_of_eq hlD).trans ((Admission.uniformDeg_le vQ L).trans (le_of_eq e'))
  have hlC0 : (layoutAt 0).C = SourceBudget.Params.COf selector sources p (requestAt coordC ph ci L tgtC modeC 0).q := hlC.trans (congrArg (SourceBudget.Params.COf selector sources p) hq.symm)
  have hK : normalizedLiveCount (requestAt coordC ph ci L tgtC modeC 0).q (requestAt coordC ph ci L tgtC modeC 0).liveScale + (requestAt coordC ph ci L tgtC modeC 0).q / 4 ≤ (requestAt coordC ph ci L tgtC modeC 0).q := by rw [hq, hL]; omega
  have hcf := NearCubicWires.SourceStart.Meta.capsFit3 selector sources p den hden _ hadm (layoutAt 0) hld hlC0 hK
  have hcf2 := hcf.2.1
  have hcf3 := hcf.2.2.1
  have hcf4 := hcf.2.2.2.1
  rw [hq, hL] at hcf2 hcf3 hcf4
  have hsm : ((requestAt coordC ph ci L tgtC modeC 0).smallSize (decompositionOf sources)) ^ (SourceBudget.DmOf packets rows SourceBudget.Params.degOf sources gamma hg hh p) ≤
      1 * RuntimeShape.smallClass 4 0 (requestAt coordC ph ci L tgtC modeC 0).q :=
    Classical.choose_spec (Classical.choose_spec (Admission.small_poly selector (decompositionOf sources) p.clauseDegree
      (ParamsV4.TW sources gamma hg hh p) (ParamsV4.LW selector mask packets rows sources gamma hg hh p)
      (SourceBudget.DmOf packets rows SourceBudget.Params.degOf sources gamma hg hh p) 4
      (ParamsV4.one_le_LW selector mask packets rows sources gamma hg hh p) (by decide))) den hsd _ hadm hLs (hq ▸ hso)
  have hrows := SourceBudget.Params.rowsFit (decompositionOf sources) hden _ hadm
  have hsmP : ((requestAt coordC ph ci L tgtC modeC 0).smallSize (decompositionOf sources)) ^ (packets (decompositionOf sources)).degree ≤
      1 * RuntimeShape.smallClass 4 0 (requestAt coordC ph ci L tgtC modeC 0).q := by
    have hD := (SourceBudget.DmOf_spec packets rows SourceBudget.Params.degOf sources gamma hg hh p).1
    rcases Nat.eq_zero_or_pos ((requestAt coordC ph ci L tgtC modeC 0).smallSize (decompositionOf sources)) with h0 | h0
    · rw [h0]
      have hc : 1 ≤ 1 * RuntimeShape.smallClass 4 0 (requestAt coordC ph ci L tgtC modeC 0).q := by
        unfold RuntimeShape.smallClass
        have := Nat.one_le_two_pow (n := (requestAt coordC ph ci L tgtC modeC 0).q / 4)
        simp only [pow_zero, one_mul]
        exact this
      rcases Nat.eq_zero_or_pos (packets (decompositionOf sources)).degree with e | e
      · rw [e, pow_zero]; exact hc
      · rw [zero_pow (by omega)]; exact Nat.zero_le _
    · exact (Nat.pow_le_pow_right h0 hD).trans hsm
  have hraw := SourceBudget.Pow2.rawFit2 selector sources p packets _ _ (SourceSteps.raw_length_le (packets (decompositionOf sources)) _) hrows hsmP
  rw [hq] at hraw
  have hgood : RowCaps.Good selector (decompositionOf sources) (printerOf sources) (requestAt coordC ph ci L tgtC modeC 0) (layoutAt 0) (factsAt 0) (capsAt 0) := by
    rw [hcapsE]
    exact SourceSkeleton.goodAt_uniform selector (decompositionOf sources) (printerOf sources) _ _ _ hcf.1 _ _ _ _ hcf2 hcf3 hcf4 hraw
  have hin := SourceBudget.Params.inFit (decompositionOf sources) hden _ hadm 𝔏𝔖 hLs
  have hgs := SourceBudget.Params.gsFit (decompositionOf sources) hden _ hadm
  obtain ⟨hMs0, hMb0, hU00⟩ := SourceBudget.Params.scalarsFit L vQ
  have hrB : r ≤ SourceBudget.Params.rB sources gamma hg hh p := by rw [hr]; exact le_of_eq rfl
  have hbF := SourceBudget.Params.bFit sources hg hh p k r n hrB
  have hQC := ClassV3.queryCap_fit selector mask packets rows sources gamma hg hh p k x bits
  have key := SourceBudget.yF0Fam_site mask packets rows SourceBudget.Params.degOf SourceBudget.Params.tgOf (ClassV4.KFc4 selector mask packets rows)
    (ClassV4.siteL4 selector mask packets rows) (ClassV4.KFc4_free selector mask packets rows) sources gamma hg hh p k n den (requestAt coordC ph ci L tgtC modeC 0)
    (layoutAt 0) (factsAt 0) (capsAt 0) (fun _ => 0) (C10PartsSchedule.entryWidthSchedule sources k r n) (InitRun.Mb L vQ) (InitPost.Ms L vQ)
    (InitRun.U0 L vQ) (SourceBudget.Params.VvOf selector sources p L (C10PartsSchedule.widthAt sources k n)) (C10PartsSchedule.entryWidthSchedule sources k r n) C hq hLs hden hadm hin
    hrows hsm hlw hld (le_of_eq hlC0)
    (by rw [hcapsE, hq, hLe]; exact SourceBudget.Pow2.hFOf2_le selector sources p _ _)
    (by rw [hcapsE, hq, hLs, hLe]; exact SourceBudget.Pow2.cCOf2_le selector sources p _ _)
    (by rw [hcapsE, hq, hLs, hLe]; exact le_trans (le_of_eq rfl) (Nat.le_add_right _ _))
    (by rw [hcapsE, hq]; exact SourceBudget.Pow2.rROf2_le selector sources p packets _)
    hgood hgs
    (by rw [hq, ← hvq]; exact hMb0) (by rw [hq, ← hvq]; exact hMs0) (by rw [hq, ← hvq]; exact hU00)
    (by rw [hq]; exact hbF) (by rw [hq]; exact hbF)
    (by rw [hq, hLs, hLe]; exact le_rfl) (Nat.zero_le _)
    (by rw [hq]; exact hC0.trans hQC)
  have e : (requestAt coordC ph ci L tgtC modeC 0).q = vQ := hq.trans hvq.symm
  have e2 : Rest.backCost (SourceBudget.seOf sources) (SourceBudget.spOf sources) (requestAt coordC ph ci L tgtC modeC 0) 0 (C10PartsSchedule.entryWidthSchedule sources k r n) (requestAt coordC ph ci L tgtC modeC 0).q
        (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC 0).family (decompositionOf sources))).gs).length (InitRun.Mb L vQ) (InitPost.Ms L vQ) =
      Rest.backCost (SourceBudget.seOf sources) (SourceBudget.spOf sources) (requestAt coordC ph ci L tgtC modeC 0) 0 (C10PartsSchedule.entryWidthSchedule sources k r n) vQ
        (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC 0).family (decompositionOf sources))).gs).length (InitRun.Mb L vQ) (InitPost.Ms L vQ) :=
    congrArg (fun t => Rest.backCost (SourceBudget.seOf sources) (SourceBudget.spOf sources) (requestAt coordC ph ci L tgtC modeC 0) 0 (C10PartsSchedule.entryWidthSchedule sources k r n) t
      (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC 0).family (decompositionOf sources))).gs).length (InitRun.Mb L vQ) (InitPost.Ms L vQ)) e
  rw [e2] at key
  exact key

end y0

end
end NearCubicWires.SourceStart.YSite
end


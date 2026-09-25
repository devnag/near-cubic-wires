import Proof.Packets.SrcYSite0
import Proof.SourceAssembly.SourceSkelWinW

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
namespace NearCubicWires.SourceSkeleton.Final
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

section resid
variable {selector : CyclicChoice.Laws} (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) {gamma : Real} (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (k r scratch : Nat)

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
local notation "𝔏" => ParamsV4.LW selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔮" => C10PartsSchedule.widthAt sources k n

def capsSite (n : Nat) : RowCaps :=
  SourceSkeleton.capsU (SourceBudget.Pow2.hFOf2 selector sources p 𝔏 𝔮) (SourceBudget.Pow2.cCOf2 selector sources p 𝔏 𝔮)
    (SourceBudget.Params.VvOf selector sources p 𝔏 𝔮) (SourceBudget.Pow2.rROf2 selector sources p packets 𝔮)

/-- **`RowCaps.Good` at every call of the clause** under the site's caps. -/
theorem goodAt_site (den : Nat) (hden : 0 < den) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (ph : Phase) (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x oracleC))
    (layoutAt : ∀ m : Nat, Packets.Layout (decompositionOf sources) ((requestAt coordC ph ci 𝔏 tgtC modeC m).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (requestAt coordC ph ci 𝔏 tgtC modeC m)))
    (factsAt : ∀ m : Nat, ∀ row ∈ ((requestAt coordC ph ci 𝔏 tgtC modeC m).family (decompositionOf sources)).rows,
      Packets.PacketFacts (decompositionOf sources) ((requestAt coordC ph ci 𝔏 tgtC modeC m).family (decompositionOf sources))
        (geometryOf selector (decompositionOf sources) (requestAt coordC ph ci 𝔏 tgtC modeC m)) row)
    (hlD : ∀ m, (layoutAt m).degree = Admission.uniformDeg vQ 𝔏)
    (hlC : ∀ m, (layoutAt m).C = SourceBudget.Params.COf selector sources p 𝔮)
    (hcut : CloseoutWitnessPolicy.inputCutoff sources ≤ n) (h201 : 201 * normalizedLiveCount 𝔮 𝔏 ≤ 𝔮)
    (hsd : ParamsV4.smallDen0W selector mask packets rows sources gamma hg hh p ≤ den)
    (hso : ParamsV4.smallOnsetW selector mask packets rows sources gamma hg hh p ≤ 𝔮) (m : Nat) :
    RowCaps.Good selector (decompositionOf sources) (printerOf sources) (requestAt coordC ph ci 𝔏 tgtC modeC m) (layoutAt m) (factsAt m)
      (capsSite mask packets rows sources hg hh p k n) := by
  obtain ⟨hadm, hq, hL⟩ := SourceSteps.site_call_facts sources p den hden k r scratch n x bits hp ph ci 𝔏 hden hcut m
  have hvq : vQ = 𝔮 := Admission.req_arity sources k (PolynomialClock.ordinaryClock k) x _ hcut
  have e' : vQ = (requestAt coordC ph ci 𝔏 tgtC modeC m).q := hvq.trans hq.symm
  have hld : (layoutAt m).degree ≤ (requestAt coordC ph ci 𝔏 tgtC modeC m).q :=
    (le_of_eq (hlD m)).trans ((Admission.uniformDeg_le vQ 𝔏).trans (le_of_eq e'))
  have hlC0 : (layoutAt m).C = SourceBudget.Params.COf selector sources p (requestAt coordC ph ci 𝔏 tgtC modeC m).q :=
    (hlC m).trans (congrArg (SourceBudget.Params.COf selector sources p) hq.symm)
  have hK : normalizedLiveCount (requestAt coordC ph ci 𝔏 tgtC modeC m).q (requestAt coordC ph ci 𝔏 tgtC modeC m).liveScale +
      (requestAt coordC ph ci 𝔏 tgtC modeC m).q / 4 ≤ (requestAt coordC ph ci 𝔏 tgtC modeC m).q := by
    rw [hq, hL]; omega
  have hcf := NearCubicWires.SourceStart.Meta.capsFit3 selector sources p den hden _ hadm (layoutAt m) hld hlC0 hK
  have hcf2 := hcf.2.1
  have hcf3 := hcf.2.2.1
  have hcf4 := hcf.2.2.2.1
  rw [hq, hL] at hcf2 hcf3 hcf4
  have hsm : ((requestAt coordC ph ci 𝔏 tgtC modeC m).smallSize (decompositionOf sources)) ^ (SourceBudget.DmOf packets rows SourceBudget.Params.degOf sources gamma hg hh p) ≤
      1 * RuntimeShape.smallClass 4 0 (requestAt coordC ph ci 𝔏 tgtC modeC m).q :=
    Classical.choose_spec (Classical.choose_spec (Admission.small_poly selector (decompositionOf sources) p.clauseDegree
      (ParamsV4.TW sources gamma hg hh p) (ParamsV4.LW selector mask packets rows sources gamma hg hh p)
      (SourceBudget.DmOf packets rows SourceBudget.Params.degOf sources gamma hg hh p) 4
      (ParamsV4.one_le_LW selector mask packets rows sources gamma hg hh p) (by decide))) den hsd _ hadm hL (hq ▸ hso)
  have hrows := SourceBudget.Params.rowsFit (decompositionOf sources) hden _ hadm
  have hsmP : ((requestAt coordC ph ci 𝔏 tgtC modeC m).smallSize (decompositionOf sources)) ^ (packets (decompositionOf sources)).degree ≤
      1 * RuntimeShape.smallClass 4 0 (requestAt coordC ph ci 𝔏 tgtC modeC m).q := by
    have hD := (SourceBudget.DmOf_spec packets rows SourceBudget.Params.degOf sources gamma hg hh p).1
    rcases Nat.eq_zero_or_pos ((requestAt coordC ph ci 𝔏 tgtC modeC m).smallSize (decompositionOf sources)) with h0 | h0
    · rw [h0]
      have hc : 1 ≤ 1 * RuntimeShape.smallClass 4 0 (requestAt coordC ph ci 𝔏 tgtC modeC m).q := by
        unfold RuntimeShape.smallClass
        have := Nat.one_le_two_pow (n := (requestAt coordC ph ci 𝔏 tgtC modeC m).q / 4)
        simp only [pow_zero, one_mul]
        exact this
      rcases Nat.eq_zero_or_pos (packets (decompositionOf sources)).degree with e | e
      · rw [e, pow_zero]; exact hc
      · rw [zero_pow (by omega)]; exact Nat.zero_le _
    · exact (Nat.pow_le_pow_right h0 hD).trans hsm
  have hraw := SourceBudget.Pow2.rawFit2 selector sources p packets _ _ (SourceSteps.raw_length_le (packets (decompositionOf sources)) _) hrows hsmP
  rw [hq] at hraw
  exact SourceSkeleton.goodAt_uniform selector (decompositionOf sources) (printerOf sources) _ _ _ hcf.1 _ _ _ _ hcf2 hcf3 hcf4 hraw

/-- **`hV1`**: `1 ≤ cVcN` from the clause's call `0` (`64 ≤ driverCap ≤ VvOf`). -/
theorem hV1_site (den : Nat) (hden : 0 < den) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (ph : Phase) (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x oracleC))
    (layoutAt : ∀ m : Nat, Packets.Layout (decompositionOf sources) ((requestAt coordC ph ci 𝔏 tgtC modeC m).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (requestAt coordC ph ci 𝔏 tgtC modeC m)))
    (hlD : ∀ m, (layoutAt m).degree = Admission.uniformDeg vQ 𝔏)
    (hlC : ∀ m, (layoutAt m).C = SourceBudget.Params.COf selector sources p 𝔮)
    (hcut : CloseoutWitnessPolicy.inputCutoff sources ≤ n) (h201 : 201 * normalizedLiveCount 𝔮 𝔏 ≤ 𝔮) :
    1 ≤ SourceBudget.Params.cVcN selector sources gamma hg hh p := by
  obtain ⟨hadm, hq, hL⟩ := SourceSteps.site_call_facts sources p den hden k r scratch n x bits hp ph ci 𝔏 hden hcut 0
  have hvq : vQ = 𝔮 := Admission.req_arity sources k (PolynomialClock.ordinaryClock k) x _ hcut
  have e' : vQ = (requestAt coordC ph ci 𝔏 tgtC modeC 0).q := hvq.trans hq.symm
  have hld : (layoutAt 0).degree ≤ (requestAt coordC ph ci 𝔏 tgtC modeC 0).q :=
    (le_of_eq (hlD 0)).trans ((Admission.uniformDeg_le vQ 𝔏).trans (le_of_eq e'))
  have hlC0 : (layoutAt 0).C = SourceBudget.Params.COf selector sources p (requestAt coordC ph ci 𝔏 tgtC modeC 0).q :=
    (hlC 0).trans (congrArg (SourceBudget.Params.COf selector sources p) hq.symm)
  have hK : normalizedLiveCount (requestAt coordC ph ci 𝔏 tgtC modeC 0).q (requestAt coordC ph ci 𝔏 tgtC modeC 0).liveScale +
      (requestAt coordC ph ci 𝔏 tgtC modeC 0).q / 4 ≤ (requestAt coordC ph ci 𝔏 tgtC modeC 0).q := by
    rw [hq, hL]; omega
  have hcf := NearCubicWires.SourceStart.Meta.capsFit3 selector sources p den hden _ hadm (layoutAt 0) hld hlC0 hK
  have hd := hcf.2.2.2.2
  have h64 : 64 ≤ RCFive.NativeResources.driverCap (decompositionOf sources) ((requestAt coordC ph ci 𝔏 tgtC modeC 0).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (requestAt coordC ph ci 𝔏 tgtC modeC 0)) (layoutAt 0) (printerOf sources) := by
    unfold RCFive.NativeResources.driverCap CloseoutRowsEstimator.Driver.value
    omega
  rw [NearCubicWires.SourceStart.Meta.VvOf_eq] at hd
  by_contra hc
  have h0 : SourceBudget.Params.cVcN selector sources gamma hg hh p = 0 := by omega
  have hm : NearCubicWires.SourceStart.Meta.mV selector sources p (requestAt coordC ph ci 𝔏 tgtC modeC 0).q = 0 := by
    unfold NearCubicWires.SourceStart.Meta.mV
    have e0 : SourceBudget.Params.v0C selector (decompositionOf sources) (printerOf sources) p.clauseDegree (SourceBudget.tgt sources p) = 0 := h0
    rw [e0, zero_mul]
  rw [hm, zero_mul] at hd
  omega

end resid

end
end NearCubicWires.SourceSkeleton.Final
end


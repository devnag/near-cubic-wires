import Proof.SourceAssembly.SourceStepsSeam5
import Proof.SourceAssembly.SourceStepsTrace5

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

section nums
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

structure SeamNums (ph : Phase)
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
    (V : Nat) (dflt : P1TopDownPaidReusable.Datum) (Dw capw logw resetw : Nat)
    (Hd : Nat → Fin (UOf mask packets rows sources res p k r) → Nat) (Ad : Nat → Fin (UOf mask packets rows sources res p k r) → List Bool)
    (old : Nat → List Bool)
    (familyCost firstCost counterReserve : Nat)
    (cW cQ cB cS refillCost N : Nat) : Prop where
  hlay : ∀ j, (lay j).degree = Admission.uniformDeg vQ L
  hL1 : 1 ≤ L
  hu : 1 ≤ vQ / (200 * (normalizedLiveCount vQ L + 1 + 1))
  hRk : Rc ≤ Rk
  hcW : Rc ≤ cW
  hcQ : Rc ≤ cQ
  hcB : Rc ≤ cB
  hcS : Rc ≤ cS
  hSl : vWS + 2 ≤ Rc
  hRl : vRW + 2 ≤ Rc
  hBl : vBF + 2 ≤ Rc
  h4b : 4*b+5 ≤ Rc
  hUl : vU0 ≤ Rc
  hMb : vMB ≤ Rc
  hMs : vMS ≤ Rc
  hKpos : ∀ x, K x → x.val < (𝔇).F ∨ ((𝔇).B + 29 + restPc se.extra sp.extra gW ≤ x.val ∧ x ≠ Dims.hrT e 𝒽 10 ∧ x ≠ Dims.hrT e 𝒽 11)
  hKpad : ∀ x, K x → (𝔇).F ≤ x.val → ZeroPadding.pad Rc (K0 x) = K0 x
  hKapp : ∀ x, K x → ∀ i, (𝒞).app i ≠ x
  hKfree : ∀ x, K x → Cycle.Free ((𝔇).slot 𝒽) ((𝔇).maskSlots 𝒽) ((𝔇).pslots 𝒽) ((𝔇).poolSlots 𝒽) ((𝔇).familySlots 𝒽) (Dims.rewind2Slots e.ext2.ext1.ext 𝒽) x ∨ x = Dims.rewind2Slots e.ext2.ext1.ext 𝒽 1 ∨ x = Dims.rewind2Slots e.ext2.ext1.ext 𝒽 2
  hKr1 : ∀ j, j < N → K (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 1) → K0 (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 1) = List.replicate (capsAt (j+1)).descriptorReserve true ∧ KH0 (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 1) = 0
  hKr2 : ∀ j, j < N → K (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 2) → K0 (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 2) = List.replicate (capsAt (j+1)).descriptorReserve false ∧ KH0 (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 2) = 0
  hj : ∀ j, j < N → j + 1 ≤ (monomials coordC ph ci).length
  hRc : ∀ j, j < N → j + 1 + 3 ≤ Rc
  hlog : ∀ j, j < N → 2 * ((requestAt coordC ph ci L tgtC modeC (j+1)).input (decompositionOf sources)).length + 1 ≤ Rc
  he1 : ∀ j, j < N → 1 ≤ PacketsGlue.RequestMeta.seedCount (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1))
  hpw : ∀ j, j < N → (CloseoutRowsCountBinary.bits (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1)))).length ≤ b
  hfirst : ∀ j, j < N → PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1)) * 2^(natBitLength (PacketsGlue.RequestMeta.seedCount (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1)))) < 2^b
  hsecond : ∀ j, j < N → PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1)) * PacketsGlue.RequestMeta.seedCount (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1)) * 2^(vQ+1) < 2^b
  hdescR : ∀ j, j < N → (capsAt (j+1)).descriptorReserve ≤ Rc
  hL : ∀ j, j < N → (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length + 3 ≤ Rc
  hfamH : ∀ j, j < N → ∀ i, r_inputH (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1))) (layA (j+1)) (factsA (j+1))) vWS vRW vBF (dataList (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1))) (layA (j+1)) (factsA (j+1))).length i + (fuelOf 𝒞 b vdX (j+1)) + 1 ≤ Rc
  hwinI : ∀ j, j < N → cursorCost j + 1 + g7cost (j+1) + 1 + (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordC ph ci L tgtC modeC (j+1)) (layA (j+1)) (factsA (j+1)) (capsAt (j+1)) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length then vMB else vMS) vU0 vWS vRW vBF b (0)) + 1 ≤ Rc
  hwinZ : ∀ j, j < N → (restCost se sp g7cost (requestAt coordC ph ci L tgtC modeC (j+1)) Rc b vQ (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length vMB vMS j) + 1 + (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordC ph ci L tgtC modeC (j+1)) (layA (j+1)) (factsA (j+1)) (capsAt (j+1)) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length then vMB else vMS) vU0 vWS vRW vBF b (0)) + 1 ≤ Rk
  hcost : ∀ j, j < N → (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordC ph ci L tgtC modeC (j+1)) (layA (j+1)) (factsA (j+1)) (capsAt (j+1)) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length then vMB else vMS) vU0 vWS vRW vBF b ((4*Rk+7) + 1 + ((4*Rc+7) + 1 + ((restCost se sp g7cost (requestAt coordC ph ci L tgtC modeC (j+1)) Rc b vQ (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length vMB vMS j) + 1 + refreshCost Rc)))) ≤ refillCost

end nums

section tnums
open NearCubicWires.SourceSkeleton NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction
attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

structure TraceNums (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
    (code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph) (ph : Phase) (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (L : Nat)
    (lay : TraceData.LayoutFamily (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) selector) (deg : Nat → Nat) (V : Nat)
    (dflt : P1TopDownPaidReusable.Datum) (Dw capw logw resetw : Nat) (old : Nat → List Bool)
    (Hd : Nat → Fin (code ph).sourceTapes → Nat) (Ad : Nat → Fin (code ph).sourceTapes → List Bool)
    (Rc familyCost refillCost firstCost counterReserve : Nat)
    (H0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) (A0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (siteFuel : Nat) (N : Nat)
    (vv : RCFive.Source.CallValues (C10TotalDecode.Atom (pcppAt sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (code ph).sourceTapes) : Prop where
  hdeg :
    ∀ j, j < (TraceData.order (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci).length →
    min (lay j).degree (Packets.pool (decompositionOf sources)
    (Packets.request sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) (SourceRequest.FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci j))
    (Packets.geometry selector
    (Packets.request sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) (SourceRequest.FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci j)))).length = deg j
  hC :
    ∀ j, j < (TraceData.order (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci).length →
    RCFive.NativeResources.streamCap (decompositionOf sources)
    (Packets.request sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) (SourceRequest.FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci j))
    (Packets.geometry selector
    (Packets.request sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) (SourceRequest.FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci j))) (lay j)
    ≤ (lay j).C
  hD :
    ∀ j, j < (TraceData.order (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci).length →
    RCFive.NativeResources.driverCap (decompositionOf sources)
    (Packets.request sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) (SourceRequest.FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci j))
    (Packets.geometry selector
    (Packets.request sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) (SourceRequest.FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci j))) (lay j)
    (code ph).a ≤ V
  hcap : 4*(C10PartsSchedule.entryWidthSchedule sources k r n)+5 ≤ capw
  hlog : 20*(C10PartsSchedule.entryWidthSchedule sources k r n)+27 ≤ logw
  h_hw :
    let rowWidth := vv.rowWidth
    let entries := vv.entries
    ∀ j<entries.length,rowWidth j≤(C10PartsSchedule.entryWidthSchedule sources k r n)
  h_hfit :
    let total := vv.total
    let entries := vv.entries
    ∀ j<entries.length,total j<2^(C10PartsSchedule.entryWidthSchedule sources k r n)
  h_hold :
    let D := vv.D
    let old := vv.old
    let entries := vv.entries
    ∀ j<entries.length,(old j).length≤D j
  h_hr :
    let resetSize := vv.resetSize
    let phasePrefix := vv.phasePrefix
    let entries := vv.entries
    ∀ j<entries.length,CloseoutFinalC10AppendPositioning.rawBudget (C10PartsSchedule.entryWidthSchedule sources k r n) (phasePrefix++entries.take j).length≤resetSize j
  h_hcost :
    let a := (code ph).a
    let xs := vv.xs
    let S := vv.S
    let rowWidth := vv.rowWidth
    let D := vv.D
    let phasePrefix := vv.phasePrefix
    let entries := vv.entries
    let familyCost := vv.familyCost
    let fuel := fun j=>f_budget a (S j) (rowWidth j) (C10PartsSchedule.entryWidthSchedule sources k r n) (xs j).length+1+
    (2*D j+4+1+(2*e_emitCost (C10PartsSchedule.entryWidthSchedule sources k r n)+2)+1+
    CloseoutFinalC10AppendPositioning.budget (C10PartsSchedule.entryWidthSchedule sources k r n) (phasePrefix++entries.take j).length)
    (∀ j<entries.length,fuel j≤familyCost)
  hbudget :
    let entries := vv.entries
    let familyCost := vv.familyCost
    let refillCost := vv.refillCost
    let firstCost := vv.firstCost
    firstCost+1+(entries.length*(familyCost+1+refillCost+3)+3) ≤ siteFuel

end tnums

end
end NearCubicWires.SourceSteps
end


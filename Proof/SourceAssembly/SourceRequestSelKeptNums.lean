import Proof.SourceAssembly.SourceStepsNums
import Proof.SourceAssembly.SourceSkelKeptW

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
namespace NearCubicWires.SourceRequest.SelKeptNums
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

/-- **The kept-set rows of `SeamNums`** (the same parameters; the six fields VERBATIM): `hKpos hKpad hKapp hKfree hKr1 hKr2`. -/
structure SeamNumsKept (ph : Phase)
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
  hKpos : ∀ x, K x → x.val < (𝔇).F ∨ ((𝔇).B + 29 + restPc se.extra sp.extra gW ≤ x.val ∧ x ≠ Dims.hrT e 𝒽 10 ∧ x ≠ Dims.hrT e 𝒽 11)
  hKpad : ∀ x, K x → (𝔇).F ≤ x.val → ZeroPadding.pad Rc (K0 x) = K0 x
  hKapp : ∀ x, K x → ∀ i, (𝒞).app i ≠ x
  hKfree : ∀ x, K x → Cycle.Free ((𝔇).slot 𝒽) ((𝔇).maskSlots 𝒽) ((𝔇).pslots 𝒽) ((𝔇).poolSlots 𝒽) ((𝔇).familySlots 𝒽) (Dims.rewind2Slots e.ext2.ext1.ext 𝒽) x ∨ x = Dims.rewind2Slots e.ext2.ext1.ext 𝒽 1 ∨ x = Dims.rewind2Slots e.ext2.ext1.ext 𝒽 2
  hKr1 : ∀ j, j < N → K (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 1) → K0 (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 1) = List.replicate (capsAt (j+1)).descriptorReserve true ∧ KH0 (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 1) = 0
  hKr2 : ∀ j, j < N → K (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 2) → K0 (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 2) = List.replicate (capsAt (j+1)).descriptorReserve false ∧ KH0 (Dims.rewind2Slots e.ext2.ext1.ext 𝒽 2) = 0

end nums

section site
variable (selector : CyclicChoice.Laws) (xtra : NearCubicWires.SourceSkeleton.Fill.XtraW selector) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

set_option hygiene false in
local notation "𝔯𝔢𝔰" => NearCubicWires.SourceSkeleton.FirstW.resSite selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔨" => NearCubicWires.SourceSkeleton.FirstW.kSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔯" => NearCubicWires.SourceSkeleton.FirstW.rSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔇𝔰" => NearCubicWires.SourceSkeleton.FirstW.DSite selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯
set_option hygiene false in
local notation "𝒽" => UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯
set_option hygiene false in
local notation "𝒞" => skelCodeR mask packets rows sources 𝔯𝔢𝔰 hres p 𝔨 𝔯 ph (refill3 mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 (𝔇𝔰).se (𝔇𝔰).sp e (g7F ph).2) (preFF ph)
set_option hygiene false in
local notation "codeF" => fun ph' => skelCodeR mask packets rows sources 𝔯𝔢𝔰 hres p 𝔨 𝔯 ph' (refill3 mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 (𝔇𝔰).se (𝔇𝔰).sp e (g7F ph').2) (preFF ph')
set_option hygiene false in
local notation "oracleC" => C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits
set_option hygiene false in
local notation "coordC" => PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x oracleC bits
set_option hygiene false in
local notation "tgtC" => C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)
set_option hygiene false in
local notation "modeC" => PCJ374c44bb8b7f47d9_.S.mode sources p den hden 𝔨 𝔯 (scratchOf mask packets rows sources 𝔯𝔢𝔰) n x bits hp
set_option hygiene false in
local notation "vQ" => (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x oracleC).arity
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
local notation "vdC" => clauseVals mask selector packets rows compiler sources p den hden 𝔨 𝔯 (scratchOf mask packets rows sources 𝔯𝔢𝔰) n x bits hp site codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt Dw capw logw resetw (oldAt coordC ph ci sources L tgtC modeC b Dw) Hd Ad Rc familyCost refillCost firstCost counterReserve

set_option hygiene false in
local notation "vdX" => clauseVals mask selector packets rows compiler sources p den hden 𝔨 𝔯 (scratchOf mask packets rows sources 𝔯𝔢𝔰) n x bits hp site codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve

theorem seamNumsKept (hres : 19 ≤ 𝔯𝔢𝔰) (ph : Phase)
    (e : (𝔇).RestExt3 (𝔇𝔰).se.extra (𝔇𝔰).sp.extra (𝔇𝔰).gW)
    (g7F : Phase → Σ s, Machine (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) s) (g7cost : Nat → Nat)
    (preFF : Phase → Σ s, Machine (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯 + 1) s)
    (compiler : Packets.CompilerLaws) (den : Nat) (hden : 0 < den) (n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden 𝔨 (PolynomialClock.ordinaryClock 𝔨))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p 𝔨 𝔯 (scratchOf mask packets rows sources 𝔯𝔢𝔰)) states)
    (ci : Fin (NC sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits))) (L : Nat) (Rc Rk b : Nat)
    (lay : TraceData.LayoutFamily coordC ph ci sources L tgtC modeC selector)
    (capsAt : Nat → RowCaps)
    (goodAt : ∀ m : Nat, RowCaps.Good selector (decompositionOf sources) (printerOf sources)
      (requestAt coordC ph ci L tgtC modeC m) (layA m) (factsA m) (capsAt m))        (V : Nat) (dflt : P1TopDownPaidReusable.Datum) (Dw capw logw resetw : Nat)
    (Hd : Nat → Fin (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) → Nat) (Ad : Nat → Fin (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) → List Bool)
    (old : Nat → List Bool)
    (familyCost firstCost counterReserve : Nat)
    (cW cQ cB cS refillCost N : Nat)
    (mode : Bool) (frameW qW : List Bool) (cdW : Fin 19 → List Bool) (resW : ℕ → List Bool) (Vv NC : ℕ)
    (hresW : ∀ i, Rc ≤ (resW i).length) (hcapsV : ∀ m, (capsAt m).descriptorReserve = Vv) :
    SeamNumsKept mask packets rows sources 𝔯𝔢𝔰 hres p 𝔨 𝔯 ph (𝔇𝔰).se (𝔇𝔰).sp e g7F g7cost preFF compiler den hden n x bits hp site ci L Rc Rk b lay
      capsAt goodAt (NearCubicWires.SourceSkeleton.KeptW.KSite selector xtra mask packets rows sources gamma hg hh p (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) mode)
      (NearCubicWires.SourceSkeleton.KeptW.K0Site selector xtra mask packets rows sources gamma hg hh p (UOf mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) (UOf_le mask packets rows sources 𝔯𝔢𝔰 p 𝔨 𝔯) mode frameW qW cdW resW Vv NC)
      (fun _ => 0) V dflt Dw capw logw resetw Hd Ad old familyCost firstCost counterReserve cW cQ cB cS refillCost N := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun x hx => NearCubicWires.SourceSkeleton.KeptW.KSite_pos selector xtra mask packets rows sources gamma hg hh p _ _ mode x hx
  · exact fun x hx hF => NearCubicWires.SourceSkeleton.KeptW.K0Site_pad selector xtra mask packets rows sources gamma hg hh p _ _ mode frameW qW cdW resW Vv NC Rc hresW x hx hF
  · intro x hx i h
    exact NearCubicWires.SourceSkeleton.KeptW.KSite_app selector xtra mask packets rows sources gamma hg hh p _ _ mode ph x hx i (by rw [← h]; rfl)
  · exact fun x hx => NearCubicWires.SourceSkeleton.KeptW.KSite_free selector xtra mask packets rows sources gamma hg hh p _ _ mode x hx
  · intro j hj hK
    rw [hcapsV]
    exact ⟨(NearCubicWires.SourceSkeleton.KeptW.K0Site_rew selector xtra mask packets rows sources gamma hg hh p _ _ mode frameW qW cdW resW Vv NC).1, rfl⟩
  · intro j hj hK
    rw [hcapsV]
    exact ⟨(NearCubicWires.SourceSkeleton.KeptW.K0Site_rew selector xtra mask packets rows sources gamma hg hh p _ _ mode frameW qW cdW resW Vv NC).2, rfl⟩

end site

end
end NearCubicWires.SourceRequest.SelKeptNums
end

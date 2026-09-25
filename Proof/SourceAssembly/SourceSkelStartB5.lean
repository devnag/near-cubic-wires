import Proof.SourceAssembly.SourceSkelStartB
import Proof.SourceAssembly.SourceStepsStart5

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
namespace NearCubicWires.SourceSkeleton.StartB5
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

/-- **`ChainStartP5` from the first seam's exit (v5).** -/
theorem chainStart_first5 (ph : Phase)
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
    (hfo5 : firstOutP5 mask packets rows sources res p k r se sp e 𝒽1 (initF ph).2 (g7G ph).2 coordC ph ci L tgtC modeC Rc Rk b layA factsA
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
    (hcR : counterReserve = Rc) (h4b : 4 * b + 5 ≤ Rc) :
    ChainStartP5 mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc Rk b lay K K0 KH0 V dflt Hd Ad
      familyCost firstCost counterReserve refillCost Rc Rc Rc Rc w0 A H H' A' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hfo5
  refine ⟨StartB.chainStart_first mask packets rows sources res hres p k r ph se sp e g7F initF g7G cnt c15 q284 c17 c18 compiler den hden n x bits hp site ci L Rc Rk b lay K K0 KH0 K1 K01 KH01 V dflt Hd Ad familyCost firstCost counterReserve refillCost w0 A H Hi H' Ai A' ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ hlowG hEncI hpay hW81 hW90 hc15 hq284 hcnt hWnc hlay hL1 hu hKpos hK hK0 hKapp hcR, ?_⟩
  intro kk hk
  rcases hk with hk | hk
  · exact a12 ⟨kk.val, hk⟩
  · have ek : kk = 4 := Fin.ext hk
    subst ek
    have e4 : A' (Dims.encT (d := 𝔇) 𝒽1 4) = ZeroPadding.pad Rc (RepairOrdinary.frame (SignedSortKey.binary b
        (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC 0) *
          PacketsGlue.RequestMeta.seedCount (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC 0) *
          2 ^ vQ))) := a7
    have hl := recordField_length_le b ⟨CompetitorValidity.Estimate.mk 0 0 1, 0,
      PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC 0) *
        PacketsGlue.RequestMeta.seedCount (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC 0) * 2 ^ vQ⟩ 4
    refine (congrArg List.length e4).trans_le ?_
    simp only [ZeroPadding.pad, List.length_append, List.length_replicate]
    have hl' : (RepairOrdinary.frame (SignedSortKey.binary b
        (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC 0) *
          PacketsGlue.RequestMeta.seedCount (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC 0) * 2 ^ vQ))).length ≤ 4*b+5 := hl
    omega

end start

end
end NearCubicWires.SourceSkeleton.StartB5
end


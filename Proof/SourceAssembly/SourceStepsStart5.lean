import Proof.SourceAssembly.SourceStepsFirstOut
import Proof.SourceAssembly.SourceStepsEntryInv4

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest
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

section fo5
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat)
  {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r

/-- **`first_seam5L`'s conclusion** (decision 99b; verbatim): `firstOutP`'s conjuncts and, LAST, the `encT 0..2` lengths at the first
cycle's exit. -/
def firstOutP5 {vE vP : PCJd4d1d9d7d1fa4313_Production.Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vE)
    (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vP) {gW : Nat}
    (e : (𝔇).RestExt3 se.extra sp.extra gW) {V : Nat} (hV : (𝔇).U ≤ V)
    {si : Nat} (initM : Machine V si) {s7 : Nat} (g7M : Machine V s7)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (L target : Nat) (mode : Bool) (Rc Rk b : Nat)
    (layoutAt : ∀ m : Nat, Packets.Layout (decompositionOf sources)
      ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m)))
    (factsAt : ∀ m : Nat, ∀ row ∈ ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources)).rows,
      Packets.PacketFacts (decompositionOf sources) ((requestAt coordinate ph ci L target mode m).family
        (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m))
        row)
    (K : Fin V → Prop) (K0 : Fin V → List Bool) (KH0 : Fin V → Nat)
    (hminj : Function.Injective ((𝔇).maskSlots hV)) (hsinj : Function.Injective ((𝔇).pslots hV))
    (hfinj : Function.Injective ((𝔇).familySlots hV)) (hpinj : Function.Injective ((𝔇).poolSlots hV))
    (hrinj : Function.Injective (Dims.rewind2Slots e.ext2.ext1.ext hV))
    (hraw : (𝔇).pslots hV (packets (decompositionOf sources)).ordinary.program.outputTape = (𝔇).familySlots hV
      ((PCJ38fbfed565f64139_Ready.headerSlots (printerOf sources) (rowWork (rows (decompositionOf sources) (printerOf sources)).privateWork) 262).castAdd 1))
    (hpool : (𝔇).poolSlots hV 34 = (𝔇).familySlots hV
      ((PCJ38fbfed565f64139_Ready.headerSlots (printerOf sources) (rowWork (rows (decompositionOf sources) (printerOf sources)).privateWork) 0).castAdd 1))
    (hsrc : Dims.rewind2Slots e.ext2.ext1.ext hV 0 = (𝔇).familySlots hV
      ((PCJ38fbfed565f64139_Ready.descriptor (printerOf sources) (rowWork (rows (decompositionOf sources) (printerOf sources)).privateWork)).castAdd 1))
    (cnt c15 q284 c17 c18 : Fin V)
    (H0 Hi : Fin V → Nat) (A0 Ai : Fin V → List Bool)
    (w Mb Ms cW cQ cB cS S Rw B v U0 fuel0 : Nat) (firstCost : Nat)
    (H' : Fin V → Nat) (A' : Fin V → List Bool) : Prop :=
      (Cycle.cycleCode mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) ((𝔇).maskSlots hV) hminj ((𝔇).pslots hV) hsinj ((𝔇).slot hV) ((𝔇).ret hV)
          ((𝔇).scr hV 0) ((𝔇).scr hV 1) ((𝔇).scr hV 2) ((𝔇).scr hV 3) ((𝔇).scr hV 4) ((𝔇).familySlots hV) hfinj
          ((𝔇).poolSlots hV) hpinj (Dims.rewind2Slots e.ext2.ext1.ext hV) hrinj hraw hpool hsrc
          ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
          (firstPro3 se sp e hV initM g7M cnt c15 q284 c17 c18) (Dims.csSlots e.ext2.ext1.ext hV) (Dims.natSlots hV) (Dims.drvSlots e.ext2.ext1.ext hV)).Prepared (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)) firstCost H0 H' A0 A' ∧
      (∀ i, H' (Dims.natSlots hV i) = r_inputH (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)) S Rw B (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)).length i) ∧
      (∀ i, A' (Dims.natSlots hV i) = ZeroPadding.pad Rc (r_inputT (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)) S Rw B
        (RowWidth.rw (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length then Mb else Ms) U0 (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length) v (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)).length i)) ∧
      (A' cnt = ZeroPadding.pad Rc (RepairSource.VerifierDecoding.CompareMachine.word (monomials coordinate ph ci).length) ∧
        H' cnt = 1) ∧
      InvR e hV Rc Rk K K0 KH0 0 w q Mb Ms cW cQ cB cS S Rw B v U0 fuel0 H' A' ∧
      (∀ kk : Fin 13, H' (Dims.encT (d := 𝔇) hV kk) = Hi (Dims.encT (d := 𝔇) hV kk)) ∧
      A' (Dims.encT (d := 𝔇) hV 4) = ZeroPadding.pad Rc (RepairOrdinary.frame (SignedSortKey.binary w
        (vP (requestAt coordinate ph ci L target mode 0) * vE (requestAt coordinate ph ci L target mode 0) * 2^q))) ∧
      (∀ hm : 0 < (monomials coordinate ph ci).length, ∀ i : Fin 3,
        A' (Dims.encT (d := 𝔇) hV ⟨i.val, by omega⟩) =
        ZeroPadding.pad Rc (RepairOrdinary.frame (CloseoutRowsEstimatorCoefficients.Stream.recordFields b
          (CloseoutFinalC10SupplierCalls.coefficientEstimate ((monomials coordinate ph ci)[0]).coefficient)
          0 0 ⟨i.val, by omega⟩))) ∧
      (∀ kk : Fin 13, (kk.val = 3 ∨ 5 ≤ kk.val) → A' (Dims.encT (d := 𝔇) hV kk) = Ai (Dims.encT (d := 𝔇) hV kk)) ∧
      (∀ x : Fin V, x.val < (𝔇).F → Cycle.Free ((𝔇).slot hV) ((𝔇).maskSlots hV) ((𝔇).pslots hV)
          ((𝔇).poolSlots hV) ((𝔇).familySlots hV) (Dims.rewind2Slots e.ext2.ext1.ext hV) x → x ≠ c15 → x ≠ q284 →
        H' x = Hi x ∧ A' x = Ai x) ∧
      (∀ x : Fin V, (𝔇).F ≤ x.val → x.val < (𝔇).U → Rc ≤ (A' x).length) ∧
      (∀ i : Fin 3, (A' (Dims.encT (d := 𝔇) hV ⟨i.val, by omega⟩)).length ≤ Rc)

end fo5

section start5
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
local notation "vdS" => clauseVals mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt (InitRun.D0 b) (InitRun.cap0 b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) (fun j => if j = 0 then w0 else oldAt coordC ph ci sources L tgtC modeC b (InitRun.D0 b) j) Hd Ad Rc familyCost refillCost firstCost counterReserve

/-- **The first cycle's exit facts, v5** (decision 99b): `ChainStartP` and (6) the `encT 0..2, 4` lengths at the exit (the chain's end when the
clause has no call). -/
def ChainStartP5 (ph : Phase)
    (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) (PacketsGlue.RequestMeta.seedCount (decompositionOf sources)))
    (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources))) {gW : Nat}
    (e : (𝔇).RestExt3 se.extra sp.extra gW)
    (g7F : Phase → Σ s, Machine (UOf mask packets rows sources res p k r) s)
    (preFF : Phase → Σ s, Machine (UOf mask packets rows sources res p k r + 1) s)
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
    (V : Nat) (dflt : P1TopDownPaidReusable.Datum)
    (Hd : Nat → Fin (UOf mask packets rows sources res p k r) → Nat) (Ad : Nat → Fin (UOf mask packets rows sources res p k r) → List Bool)
    (familyCost firstCost counterReserve refillCost : Nat) (cW cQ cB cS : Nat) (w0 : List Bool)
    (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)) → List Bool) (H : Fin (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)) → Nat)
    (H' : Fin ((𝒞).sourceTapes + 1) → Nat) (A' : Fin ((𝒞).sourceTapes + 1) → List Bool) : Prop :=
  ChainStartP mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc Rk b lay K K0 KH0 V dflt Hd Ad familyCost firstCost counterReserve refillCost cW cQ cB cS w0 A H H' A' ∧
  (∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → (A' (Dims.encT (d := 𝔇) (UOf_le_succ mask packets rows sources res p k r) kk)).length ≤ Rc)

/-- **THE FIRST-ENTRY HOLE at one clause, v5** (decisions 95, 99b): `StartHole4` at `ChainStartP5`. `StartHole` at `entryInvAt4` (the first branch carries `InitS.QueryAt`). Every `entryInvAt4` bank of clause `ci` has a first-cycle exit
with `ChainStartP`, the call-0 payload read off the entry's `encT 5`. -/
def StartHole5 (ph : Phase)
    (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) (PacketsGlue.RequestMeta.seedCount (decompositionOf sources)))
    (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) (PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources))) {gW : Nat}
    (e : (𝔇).RestExt3 se.extra sp.extra gW)
    (g7F : Phase → Σ s, Machine (UOf mask packets rows sources res p k r) s)
    (preFF : Phase → Σ s, Machine (UOf mask packets rows sources res p k r + 1) s)
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
    (V : Nat) (dflt : P1TopDownPaidReusable.Datum)
    (Hd : Nat → Fin (UOf mask packets rows sources res p k r) → Nat) (Ad : Nat → Fin (UOf mask packets rows sources res p k r) → List Bool)
    (familyCost firstCost counterReserve refillCost : Nat) (cW cQ cB cS : Nat)
    (E : EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res))) (EF : Phase → Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) → List CloseoutRowsEstimatorCoefficients.Stream.Entry) : Prop :=
  ∀ (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)) → List Bool) (H : Fin (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res)) → Nat),
    entryInvAt4 sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp E EF ph ci.val A H →
    ∃ (H' : Fin ((𝒞).sourceTapes + 1) → Nat) (A' : Fin ((𝒞).sourceTapes + 1) → List Bool),
      ChainStartP5 mask packets rows sources res hres p k r ph se sp e g7F preFF compiler den hden n x bits hp site ci L Rc Rk b lay K K0 KH0 V dflt Hd Ad familyCost firstCost counterReserve refillCost cW cQ cB cS
        ((A ((𝒞).whole (Dims.encT (d := 𝔇) 𝒽 5).castSucc)).take (InitRun.D0 b)) A H H' A'

end start5

end
end NearCubicWires.SourceSteps
end


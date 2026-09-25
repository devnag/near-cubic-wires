import Proof.SourceAssembly.SourceSkelGenS

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceSkeleton
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

structure LoopContract2 (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
    (code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph)
    (sf : Phase → Nat) where
  Inv0 : Phase → (Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) → (Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) → Prop
  InvN : Phase → (Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) → (Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) → Prop
  loop : ∀ (ph : Phase) (A0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (H0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat), Inv0 ph A0 H0 →
    LoopOut mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph (sf ph) A0 H0
      (InvN ph)
  pen0 : Inv0 .penalty (penaltyA0 sources p den hden k r scratch n x bits hp) (fun j => (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j))
  bridge : ∀ (ph ph' : Phase), (ph = .penalty ∧ ph' = .moment) ∨ (ph = .moment ∧ ph' = .clause) →
    ∀ (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (H : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) (A' : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool) (H' : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → Nat),
      InvN ph A H →
      (∀ t, (∀ j, Wd sources p k r scratch ph j ≠ t) → (∀ j, Fd sources p k r scratch ph j ≠ t) →
        A' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = A t) →
      (∀ t, H' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = H t) →
      (∀ i : Fin 218, (i = 0 ∨ i = 1 ∨ i = 216 ∨ i = 217) →
        A' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Fd sources p k r scratch ph (i.castAdd 1))) =
          A (Fd sources p k r scratch ph (i.castAdd 1))) →
      Inv0 ph' (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A')
        (fun i => H' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch i))

def selectedOfContract2 {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den : Nat} {hden : 0 < den} {k r scratch n : Nat} {x : BitInput n} {bits : List Bool} {hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true} {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states} {remainingFuel : Nat} {width : Phase → Nat} {code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}
    (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder)
    (S : CloseoutFinalC10ModeNativeSchedule.Selection sources p k) (hn : S.onset ≤ n) (hr : r = S.exponent)
    (sf : Phase → Nat)
    (K : LoopContract2 mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code sf)
    (hwidth : ∀ ph, width ph = CompetitorSumWidth.width (Poly sources p k den (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits ph).monomials.length
      (CompetitorRationalDecision.width (C10PartsSchedule.entryWidthSchedule sources k r n)))
    (fits : PCJ374c44bb8b7f47d9_.branchFuel (costOf sources p den k r n x bits sf) width + 2 ≤ remainingFuel) :
    SelectedWitness mask selector packets rows compiler sources p den hden k r scratch n x bits hp
      site remainingFuel width code :=
  let Po := K.loop .penalty (penaltyA0 sources p den hden k r scratch n x bits hp) (fun j => (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j)) K.pen0
  let wp := penaltyW S hn hr Po.L Po.hA0 Po.hH0 Po.liveScale Po.hL Po.hT
    (cpOf sources p k n x bits sf .penalty) (cp_le sf .penalty Po.L Po.hsf) (cost_eq sf .penalty Po.L)
    ((hwidth .penalty).trans (width_eq .penalty Po.L))
  let Mo := K.loop .moment (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) (xA tables semantics buildSource wp))
    (fun i => xH tables semantics buildSource wp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch i))
    (K.bridge .penalty .moment (Or.inl ⟨rfl, rfl⟩) (Po.L.A (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (Po.L.H (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)))
      (xA tables semantics buildSource wp) (xH tables semantics buildSource wp) Po.hexit
      (fun t hW hF => exit_frame tables semantics buildSource wp t hW hF)
      (fun t => exit_heads tables semantics buildSource wp t)
      (fun i hi => exit_protected tables semantics buildSource wp i hi))
  let wm := laterW (Or.inl rfl) S hn hr (penalty_bank sources p den hden k r scratch n x bits hp).1
    (pen_later tables semantics buildSource wp Po.L.exits (fun t => congrFun Po.hA0 t) (fun t => congrFun Po.hH0 t)
      .moment (Or.inl rfl))
    Mo.L Mo.hA0 Mo.hH0 Mo.liveScale Mo.hL Mo.hT
    (cpOf sources p k n x bits sf .moment) (cp_le sf .moment Mo.L Mo.hsf) (cost_eq sf .moment Mo.L)
    ((hwidth .moment).trans (width_eq .moment Mo.L))
  let Co := K.loop .clause (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) (xA tables semantics buildSource wm))
    (fun i => xH tables semantics buildSource wm (PCJda54a286946142d3_BranchPhases.body sources p k r scratch i))
    (K.bridge .moment .clause (Or.inr ⟨rfl, rfl⟩) (Mo.L.A (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (Mo.L.H (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)))
      (xA tables semantics buildSource wm) (xH tables semantics buildSource wm) Mo.hexit
      (fun t hW hF => exit_frame tables semantics buildSource wm t hW hF)
      (fun t => exit_heads tables semantics buildSource wm t)
      (fun i hi => exit_protected tables semantics buildSource wm i hi))
  SelectedWitness.ofLoops tables semantics buildSource (costOf sources p den k r n x bits sf) S hn hr
    Po.L Po.hA0 Po.hH0 Po.liveScale Po.hL Po.hT
    (cpOf sources p k n x bits sf .penalty) (cp_le sf .penalty Po.L Po.hsf) (cost_eq sf .penalty Po.L)
    ((hwidth .penalty).trans (width_eq .penalty Po.L))
    Mo.L Mo.hA0 Mo.hH0 Mo.liveScale Mo.hL Mo.hT
    (cpOf sources p k n x bits sf .moment) (cp_le sf .moment Mo.L Mo.hsf) (cost_eq sf .moment Mo.L)
    ((hwidth .moment).trans (width_eq .moment Mo.L))
    Co.L Co.hA0 Co.hH0 Co.liveScale Co.hL Co.hT
    (cpOf sources p k n x bits sf .clause) (cp_le sf .clause Co.L Co.hsf) (cost_eq sf .clause Co.L)
    ((hwidth .clause).trans (width_eq .clause Co.L))
    fits

structure StepsContract2 (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
    (code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph) (sf : Phase → Nat) where
  Inv : Phase → Nat → (Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) → (Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) → Prop
  steps : ∀ ph, ClauseSteps mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph (sf ph) (Inv ph)
  pen0 : Inv .penalty 0 (penaltyA0 sources p den hden k r scratch n x bits hp) (fun j => (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j))
  bridge : ∀ (ph ph' : Phase), (ph = .penalty ∧ ph' = .moment) ∨ (ph = .moment ∧ ph' = .clause) →
    ∀ (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (H : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) (A' : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool) (H' : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → Nat),
      Inv ph (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) A H →
      (∀ t, (∀ j, Wd sources p k r scratch ph j ≠ t) → (∀ j, Fd sources p k r scratch ph j ≠ t) →
        A' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = A t) →
      (∀ t, H' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) = H t) →
      (∀ i : Fin 218, (i = 0 ∨ i = 1 ∨ i = 216 ∨ i = 217) →
        A' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Fd sources p k r scratch ph (i.castAdd 1))) =
          A (Fd sources p k r scratch ph (i.castAdd 1))) →
      Inv ph' 0 (laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) A')
        (fun i => H' (PCJda54a286946142d3_BranchPhases.body sources p k r scratch i))

/-- **`LoopContract` from the steps contract.** -/
def contractOfSteps2 {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den : Nat} {hden : 0 < den} {k r scratch n : Nat} {x : BitInput n} {bits : List Bool} {hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true} {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states} {code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph} {sf : Phase → Nat}
    (K : StepsContract2 mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code sf) : LoopContract2 mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code sf where
  Inv0 := fun ph => K.Inv ph 0
  InvN := fun ph => K.Inv ph (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))
  loop := fun ph A0 H0 h0 => loopOutOfSteps (K.steps ph) A0 H0 h0
  pen0 := K.pen0
  bridge := K.bridge

/-- **THE LOOPS HOLE** for any code family. -/
def LoopsHoleG2 (mask : MaskProducer) {selector : CyclicChoice.Laws}
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (res : ResChoice) (f : FreeChoices) (code : SourceParent.CodeFamily mask selector packets rows (forcedChoices mask packets rows res f)) (sf : SiteFuelFam) : Type :=
  (sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) →
    (p : Parameters sources gamma) → (n : Nat) → (x : BitInput n) → (bits : List Bool) →
    let ch := forcedChoices mask packets rows res f
    let C := ControllerCappedRuntime.continuation sources p (ch.capIndex sources gamma hg hh p+1)
      (ch.remainingDegree sources gamma hg hh p) (ch.r sources gamma hg hh p)
      (ch.base sources gamma hg hh p) (ch.scratch sources gamma hg hh p)
      (code.site sources gamma hg hh p) (ch.remainingFuel sources gamma hg hh p)
    (hn : (ControllerCappedSelected.workerData sources p (ch.capIndex sources gamma hg hh p+1)
      (Nat.succ_pos (ch.capIndex sources gamma hg hh p))
      (ControllerCappedSelected.programData (ch.capIndex sources gamma hg hh p+1) C)).onset ≤ n) →
    (hp : (ControllerCappedSelected.workerData sources p (ch.capIndex sources gamma hg hh p+1)
      (Nat.succ_pos (ch.capIndex sources gamma hg hh p))
      (ControllerCappedSelected.programData (ch.capIndex sources gamma hg hh p+1) C)).passed n x bits = true) →
    LoopContract2 mask selector packets rows compiler sources p (ch.capIndex sources gamma hg hh p+1)
      (Nat.succ_pos (ch.capIndex sources gamma hg hh p)) C.k
      (ch.r sources gamma hg hh p) (ch.scratch sources gamma hg hh p) n x bits hp
      (code.site sources gamma hg hh p)
      (fun ph => code sources gamma hg hh p
        (PCJ374c44bb8b7f47d9_.S.mode sources p (ch.capIndex sources gamma hg hh p+1)
          (Nat.succ_pos (ch.capIndex sources gamma hg hh p)) C.k
          (ch.r sources gamma hg hh p) (ch.scratch sources gamma hg hh p) n x bits hp) ph)
      (sf sources gamma hg hh p n x bits)

/-- **THE PER-CLAUSE HOLE** for any code family. -/
def StepsHoleG2 (mask : MaskProducer) {selector : CyclicChoice.Laws}
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (res : ResChoice) (f : FreeChoices) (code : SourceParent.CodeFamily mask selector packets rows (forcedChoices mask packets rows res f)) (sf : SiteFuelFam) : Type :=
  (sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) →
    (p : Parameters sources gamma) → (n : Nat) → (x : BitInput n) → (bits : List Bool) →
    let ch := forcedChoices mask packets rows res f
    let C := ControllerCappedRuntime.continuation sources p (ch.capIndex sources gamma hg hh p+1)
      (ch.remainingDegree sources gamma hg hh p) (ch.r sources gamma hg hh p)
      (ch.base sources gamma hg hh p) (ch.scratch sources gamma hg hh p)
      (code.site sources gamma hg hh p) (ch.remainingFuel sources gamma hg hh p)
    (hn : (ControllerCappedSelected.workerData sources p (ch.capIndex sources gamma hg hh p+1)
      (Nat.succ_pos (ch.capIndex sources gamma hg hh p))
      (ControllerCappedSelected.programData (ch.capIndex sources gamma hg hh p+1) C)).onset ≤ n) →
    (hp : (ControllerCappedSelected.workerData sources p (ch.capIndex sources gamma hg hh p+1)
      (Nat.succ_pos (ch.capIndex sources gamma hg hh p))
      (ControllerCappedSelected.programData (ch.capIndex sources gamma hg hh p+1) C)).passed n x bits = true) →
    StepsContract2 mask selector packets rows compiler sources p (ch.capIndex sources gamma hg hh p+1)
      (Nat.succ_pos (ch.capIndex sources gamma hg hh p)) C.k
      (ch.r sources gamma hg hh p) (ch.scratch sources gamma hg hh p) n x bits hp
      (code.site sources gamma hg hh p)
      (fun ph => code sources gamma hg hh p
        (PCJ374c44bb8b7f47d9_.S.mode sources p (ch.capIndex sources gamma hg hh p+1)
          (Nat.succ_pos (ch.capIndex sources gamma hg hh p)) C.k
          (ch.r sources gamma hg hh p) (ch.scratch sources gamma hg hh p) n x bits hp) ph)
      (sf sources gamma hg hh p n x bits)

/-- The loops hole from the per-clause hole. -/
def loopsOfStepsG2 (mask : MaskProducer) {selector : CyclicChoice.Laws}
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (res : ResChoice) (f : FreeChoices) (code : SourceParent.CodeFamily mask selector packets rows (forcedChoices mask packets rows res f)) (sf : SiteFuelFam)
    (K : StepsHoleG2 mask packets rows compiler res f code sf) : LoopsHoleG2 mask packets rows compiler res f code sf :=
  fun sources gamma hg hh p n x bits hn hp => contractOfSteps2 (K sources gamma hg hh p n x bits hn hp)

/-- The obligations, from the holes, at ANY Selection family. -/
def obligationsOfS2 (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder)
    (mask : MaskProducer) {selector : CyclicChoice.Laws}
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (S : SelFam)
    (res : ResChoice) (f : FreeChoices) (code : SourceParent.CodeFamily mask selector packets rows (forcedChoices mask packets rows res f))
    (hr : ∀ sources gamma hg hh p, f.r sources gamma hg hh p =
      (S sources p (kOf f.capIndex f.remainingDegree sources gamma hg hh p)).exponent)
    (hbase : ∀ sources gamma hg hh p, (S sources p
      (kOf f.capIndex f.remainingDegree sources gamma hg hh p)).onset ≤ f.base sources gamma hg hh p)
    (sf : SiteFuelFam) (loops : LoopsHoleG2 mask packets rows compiler res f code sf)
    (fits : FitsHoleG mask packets rows res f code sf) :
    SourceObligations mask selector packets rows compiler (forcedChoices mask packets rows res f) code :=
  fun sources gamma hg hh p n x bits hn hp =>
    selectedOfContract2 tables semantics buildSource
      (S sources p (kOf f.capIndex f.remainingDegree sources gamma hg hh p))
      ((hbase sources gamma hg hh p).trans ((base_le_onset sources p _ (Nat.succ_pos (f.capIndex sources gamma hg hh p))
        _).trans hn))
      (hr sources gamma hg hh p)
      (sf sources gamma hg hh p n x bits) (loops sources gamma hg hh p n x bits hn hp)
      (fun _ => rfl) (fits sources gamma hg hh p n x bits hn hp)

/-- **THE GENERIC FILL at any Selection family.** -/
theorem source_target_genS2 (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
    (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
    (tables : PCJ9eff70d512234a4c_Fixed.TableCertificate) (semantics : PCJ9eff70d512234a4c_Fixed.Certificate)
    (S : SelFam)
    (res : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
      PCJc4297ab269d8423a_Source.RowLibrary selector → ResChoice)
    (f : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
      PCJc4297ab269d8423a_Source.RowLibrary selector → FreeChoices)
    (hr : ∀ mask packets rows sources gamma hg hh p, (f mask packets rows).r sources gamma hg hh p =
      (S sources p (kOf (f mask packets rows).capIndex (f mask packets rows).remainingDegree sources gamma hg hh p)).exponent)
    (hbase : ∀ mask packets rows sources gamma hg hh p, (S sources p
      (kOf (f mask packets rows).capIndex (f mask packets rows).remainingDegree sources gamma hg hh p)).onset ≤
        (f mask packets rows).base sources gamma hg hh p)
    (code : ∀ mask packets rows, SourceParent.CodeFamily mask selector packets rows
      (forcedChoices mask packets rows (res mask packets rows) (f mask packets rows)))
    (sf : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
      PCJc4297ab269d8423a_Source.RowLibrary selector → SiteFuelFam)
    (steps : ∀ mask packets rows, StepsHoleG2 mask packets rows compiler (res mask packets rows) (f mask packets rows)
      (code mask packets rows) (sf mask packets rows))
    (fits : ∀ mask packets rows, FitsHoleG mask packets rows (res mask packets rows) (f mask packets rows)
      (code mask packets rows) (sf mask packets rows))
    (split : ∀ mask packets rows, RuntimeShape.SplitRuntime
      (choicesOf (forcedChoices mask packets rows (res mask packets rows) (f mask packets rows)) (code mask packets rows))) :
    PCJc4297ab269d8423a_Source.RemainingSource (fun {q m K} => @selector q m K) compiler tables semantics :=
  RuntimeShape.remainingSource_of_split selector compiler tables semantics
    (fun mask packets rows buildSource =>
      ⟨choicesOf (forcedChoices mask packets rows (res mask packets rows) (f mask packets rows)) (code mask packets rows),
       physical_of_contract tables semantics buildSource
        ⟨forcedChoices mask packets rows (res mask packets rows) (f mask packets rows), code mask packets rows,
         obligationsOfS2 tables semantics buildSource mask packets rows compiler S (res mask packets rows)
          (f mask packets rows) (code := code mask packets rows) (hr mask packets rows) (hbase mask packets rows)
          (sf mask packets rows)
          (loopsOfStepsG2 mask packets rows compiler (res mask packets rows) (f mask packets rows)
            (code := code mask packets rows) (sf mask packets rows) (steps mask packets rows))
          (fits mask packets rows)⟩,
       split mask packets rows⟩)

/-- **The grouped source hole, every tunable inside** (decisions 77/78): a Selection family, the reserved region, the free choices (the
record-width exponent, the classes, `capIndex`, the base/onset, the fuels), the code family and the site fuel; then the two Selection
facts, the per-clause steps, the J5 fits and the runtime split. -/
def SourceGenHoles3 (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
    (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws) : Prop :=
  ∃ (S : SelFam)
    (res : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
      PCJc4297ab269d8423a_Source.RowLibrary selector → ResChoice)
    (f : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
      PCJc4297ab269d8423a_Source.RowLibrary selector → FreeChoices)
    (code : ∀ mask packets rows, SourceParent.CodeFamily mask selector packets rows
      (forcedChoices mask packets rows (res mask packets rows) (f mask packets rows)))
    (sf : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
      PCJc4297ab269d8423a_Source.RowLibrary selector → SiteFuelFam),
    (∀ mask packets rows sources gamma hg hh p, (f mask packets rows).r sources gamma hg hh p =
      (S sources p (kOf (f mask packets rows).capIndex (f mask packets rows).remainingDegree sources gamma hg hh p)).exponent) ∧
    (∀ mask packets rows sources gamma hg hh p, (S sources p
      (kOf (f mask packets rows).capIndex (f mask packets rows).remainingDegree sources gamma hg hh p)).onset ≤
        (f mask packets rows).base sources gamma hg hh p) ∧
    Nonempty (∀ mask packets rows, StepsHoleG2 mask packets rows compiler (res mask packets rows) (f mask packets rows)
      (code mask packets rows) (sf mask packets rows)) ∧
    (∀ mask packets rows, FitsHoleG mask packets rows (res mask packets rows) (f mask packets rows)
      (code mask packets rows) (sf mask packets rows)) ∧
    (∀ mask packets rows, RuntimeShape.SplitRuntime
      (choicesOf (forcedChoices mask packets rows (res mask packets rows) (f mask packets rows)) (code mask packets rows)))

theorem source_of_gen3 (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
    (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
    (tables : PCJ9eff70d512234a4c_Fixed.TableCertificate) (semantics : PCJ9eff70d512234a4c_Fixed.Certificate)
    (h : SourceGenHoles3 selector compiler) :
    PCJc4297ab269d8423a_Source.RemainingSource (fun {q m K} => @selector q m K) compiler tables semantics := by
  obtain ⟨S, res, f, code, sf, hr, hbase, ⟨steps⟩, fits, split⟩ := h
  exact source_target_genS2 selector compiler tables semantics S res f hr hbase code sf steps fits split

end
end NearCubicWires.SourceSkeleton
end


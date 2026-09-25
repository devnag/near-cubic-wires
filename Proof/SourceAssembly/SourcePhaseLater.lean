import Proof.SourceAssembly.SourcePhaseDen

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourcePhase
open NearCubicWires.SourceParent
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

/-! ## 1. Slot numbers, and when a fold keeps a tape -/

section slots
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k r scratch : Nat)

theorem wd_cases (ph : Phase) (i : Fin 278) :
    ((Wd sources p k r scratch ph i).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 126 + 2*(C10TailUniformSlots.phaseIndex ph).val ∧ i.val = 274) ∨
    ((Wd sources p k r scratch ph i).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 127 + 2*(C10TailUniformSlots.phaseIndex ph).val ∧ i.val = 275) ∨
    ((Wd sources p k r scratch ph i).val = i.val ∧ i.val ≠ 274 ∧ i.val ≠ 275 ∧
      (i.val = 0 ∨ i.val = 1 ∨ i.val = 216 ∨ i.val = 217 ∨ (C10TailUniformSlots.phaseIndex ph).val = 0)) ∨
    ((Wd sources p k r scratch ph i).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 599 + ((C10TailUniformSlots.phaseIndex ph).val-1)*278 + i.val ∧ i.val ≠ 274 ∧ i.val ≠ 275 ∧
      i.val ≠ 0 ∧ i.val ≠ 1 ∧ i.val ≠ 216 ∧ i.val ≠ 217 ∧ (C10TailUniformSlots.phaseIndex ph).val ≠ 0) := by
  rw [wd_val]
  split_ifs <;> omega

theorem fd_cases (ph : Phase) (j : Fin 219) :
    ((Fd sources p k r scratch ph j).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 342 + (C10TailUniformSlots.phaseIndex ph).val ∧ j.val = 215) ∨
    ((Fd sources p k r scratch ph j).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 132 + (C10TailUniformSlots.phaseIndex ph).val ∧ j.val = 218) ∨
    ((Fd sources p k r scratch ph j).val = j.val ∧ j.val ≠ 215 ∧ j.val ≠ 218 ∧
      (j.val = 0 ∨ j.val = 1 ∨ j.val = 216 ∨ j.val = 217 ∨ (C10TailUniformSlots.phaseIndex ph).val = 0)) ∨
    ((Fd sources p k r scratch ph j).val = PCJda54a286946142d3_BranchPhases.offset sources p k r + 599 + ((C10TailUniformSlots.phaseIndex ph).val-1)*278 + j.val ∧ j.val ≠ 215 ∧ j.val ≠ 218 ∧
      j.val ≠ 0 ∧ j.val ≠ 1 ∧ j.val ≠ 216 ∧ j.val ≠ 217 ∧ (C10TailUniformSlots.phaseIndex ph).val ≠ 0) := by
  rw [fd_val]
  split_ifs <;> omega

/-- A phase's fold keeps every tape above the low bank off its four tail ports and its own bank. -/
theorem keeps_of (ph : Phase) (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (h278 : 278 ≤ t.val)
    (hA : t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 126 + 2*(C10TailUniformSlots.phaseIndex ph).val) (hB : t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 127 + 2*(C10TailUniformSlots.phaseIndex ph).val)
    (hC : t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 342 + (C10TailUniformSlots.phaseIndex ph).val) (hD : t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 132 + (C10TailUniformSlots.phaseIndex ph).val)
    (hE : (C10TailUniformSlots.phaseIndex ph).val = 0 ∨ t.val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 599 + ((C10TailUniformSlots.phaseIndex ph).val-1)*278 ∨ PCJda54a286946142d3_BranchPhases.offset sources p k r + 599 + ((C10TailUniformSlots.phaseIndex ph).val-1)*278 + 278 ≤ t.val) :
    FoldKeeps sources p k r scratch ph t := by
  left
  constructor
  · intro j he
    have hv := congrArg Fin.val he
    have hj := j.isLt
    rcases wd_cases sources p k r scratch ph j with h | h | h | h <;> omega
  · intro j he
    have hv := congrArg Fin.val he
    have hj := j.isLt
    rcases fd_cases sources p k r scratch ph j with h | h | h | h <;> omega

/-- Tape 217 is a protected fold slot of every phase. -/
theorem keeps_217 (ph : Phase) (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (ht : t.val = 217) : FoldKeeps sources p k r scratch ph t := by
  right
  refine ⟨⟨t.val, by omega⟩, Or.inr (Or.inr (Or.inr (Fin.ext ht))), ?_⟩
  apply Fin.ext
  rw [fd_val]
  simp only [Fin.val_castAdd]
  split_ifs <;> omega

theorem wd_nc (mode : Bool) (ph : Phase) (i : Fin 278) (h2 : 2 ≤ i.val) :
    ∀ j, Wd sources p k r scratch ph i ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode j :=
  not_cache sources p k r scratch mode _ (wd_ge_two ph i h2) (wordSlots_region _ _ _ _ ph i)

theorem fd_nc (mode : Bool) (ph : Phase) (i : Fin 219) (h2 : 2 ≤ i.val) :
    ∀ j, Fd sources p k r scratch ph i ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode j :=
  not_cache sources p k r scratch mode _ (fd_ge_two ph i h2) (foldSlots_region _ _ _ _ ph i)

end slots

/-! ## 2. J3 -/

/-- **J3 (`threshold`)** at the schedule width: the threshold floor is a summand of `b`. -/
theorem phase_threshold (sources : EightSources) (k r n : Nat) (entries : List Stream.Entry) :
    C10ThresholdWidths.thresholdWidth (constantsOf sources) ≤
      CloseoutFinalC10WorkerFold.foldWidth (CompetitorRationalDecision.width (C10PartsSchedule.entryWidthSchedule sources k r n)) entries := by
  have key : ∀ a w m : Nat, a ≤ (m+1)*(2*(a+w)+2+1) := by
    intro a w m
    calc a ≤ 2*(a+w)+2+1 := by omega
      _ = 1*(2*(a+w)+2+1) := (one_mul _).symm
      _ ≤ (m+1)*(2*(a+w)+2+1) := Nat.mul_le_mul_right _ (by omega)
  exact key _ _ _

/-! ## 3. What a later phase needs of its entry bank -/

section later
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k r scratch : Nat)
  (clock : OrdinaryClock (fun n => n^(k+2))) {n : Nat} (x : BitInput n)
  (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))

/-- **The entry bank of a moment/clause phase** (the previous phase's exit), as its loop start needs it. -/
structure LaterIn (mode : Bool) (ph : Phase) (b : Nat) (hin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → Nat) (tin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool) : Prop where
  blank : ∀ i : Fin 278, 2 ≤ i.val → i.val < 215 → i.val ≠ 81 → i.val ≠ 90 →
    tin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Wd sources p k r scratch ph i)) = []
  fresh : ∀ i : Fin 278, 219 ≤ i.val → tin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Wd sources p k r scratch ph i)) = []
  record : tin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Fd sources p k r scratch ph 215)) = []
  log : tin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Fd sources p k r scratch ph 218)) = []
  driver : tin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Wd sources p k r scratch ph 218)) = List.replicate b true
  stream : tin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Wd sources p k r scratch ph 81)) = []
  count : tin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Wd sources p k r scratch ph 90)) = CompareMachine.word 0
  cache : ∀ i, tin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i)) = CD sources k clock x oracle (NC sources k clock x oracle) i
  cacheH : ∀ i, hin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i)) = 0
  termH : hin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch)) = 0
  countT : tin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch)) = List.replicate (NC sources k clock x oracle) true
  Hw : ∀ i, hin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Wd sources p k r scratch ph i)) = 0
  Hf : ∀ i, hin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (Fd sources p k r scratch ph i)) = 0
  driverH : hin (PCJda54a286946142d3_BranchPhases.driver sources p k r scratch) = 1
  driverT : tin (PCJda54a286946142d3_BranchPhases.driver sources p k r scratch) = UnaryTemplate.tape (NC sources k clock x oracle)

/-- The later loop start, in exactly the forms `PhaseWitness.ofLoop` takes. -/
theorem later_facts (mode : Bool) (ph : Phase) (b : Nat) (hin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → Nat) (tin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool)
    (hI : LaterIn sources p k r scratch clock x oracle mode ph b hin tin) :
    (∀ i : Fin 278, 2 ≤ i.val → i.val < 215 → i.val ≠ 81 → i.val ≠ 90 →
      laterA0 sources p k r scratch clock x oracle mode tin (Wd sources p k r scratch ph i) = []) ∧
    (∀ i : Fin 278, 219 ≤ i.val → laterA0 sources p k r scratch clock x oracle mode tin (Wd sources p k r scratch ph i) = []) ∧
    laterA0 sources p k r scratch clock x oracle mode tin (Fd sources p k r scratch ph 215) = [] ∧
    laterA0 sources p k r scratch clock x oracle mode tin (Fd sources p k r scratch ph 218) = [] ∧
    laterA0 sources p k r scratch clock x oracle mode tin (Wd sources p k r scratch ph 218) = List.replicate b true ∧
    laterA0 sources p k r scratch clock x oracle mode tin (Wd sources p k r scratch ph 81) = [] ∧
    laterA0 sources p k r scratch clock x oracle mode tin (Wd sources p k r scratch ph 90) = CompareMachine.word 0 ∧
    laterA0 sources p k r scratch clock x oracle mode tin (PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch) = List.replicate (NC sources k clock x oracle) true ∧
    (∀ i, laterA0 sources p k r scratch clock x oracle mode tin (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) = CD sources k clock x oracle 0 i) := by
  have off := laterA0_off sources p k r scratch clock x oracle mode tin
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i h2 h3 h4 h5
    rw [off _ (fun j he => wd_nc sources p k r scratch mode ph i h2 j he)]
    exact hI.blank i h2 h3 h4 h5
  · intro i h
    rw [off _ (fun j he => wd_nc sources p k r scratch mode ph i (by omega) j he)]
    exact hI.fresh i h
  · rw [off _ (fun j he => fd_nc sources p k r scratch mode ph 215 (by decide) j he)]
    exact hI.record
  · rw [off _ (fun j he => fd_nc sources p k r scratch mode ph 218 (by decide) j he)]
    exact hI.log
  · rw [off _ (fun j he => wd_nc sources p k r scratch mode ph 218 (by decide) j he)]
    exact hI.driver
  · rw [off _ (fun j he => wd_nc sources p k r scratch mode ph 81 (by decide) j he)]
    exact hI.stream
  · rw [off _ (fun j he => wd_nc sources p k r scratch mode ph 90 (by decide) j he)]
    exact hI.count
  · rw [off _ (fun j he => PCJ30aa6f1b7c2a4221_.Selected.cache_ne_terminal sources p k r scratch mode j he.symm)]
    exact hI.countT
  · exact laterA0_cache sources p k r scratch clock x oracle mode tin hI.cache

theorem later_word (mode : Bool) (tin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool) (w : List Bool) (h : tin (PCJda54a286946142d3_BranchPhases.driver sources p k r scratch) = w) :
    laterMiddle sources p k r scratch clock x oracle mode tin (PCJda54a286946142d3_BranchPhases.driver sources p k r scratch) = w := by
  unfold laterMiddle
  rw [install_other _ _ _ _ (fun i he => PCJda54a286946142d3_BranchPhases.body_ne_driver sources p k r scratch i he)]
  exact h

theorem later_tape (mode : Bool) (tin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool) (i : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) :
    laterMiddle sources p k r scratch clock x oracle mode tin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch i) =
      laterA0 sources p k r scratch clock x oracle mode tin i :=
  install_slot _ (PCJda54a286946142d3_BranchPhases.body_injective sources p k r scratch) _ _ i

end later

theorem penalty_tape (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true) (i : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) :
    penaltyMiddle sources p den hden k r scratch n x bits hp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch i) =
      penaltyA0 sources p den hden k r scratch n x bits hp i :=
  install_slot _ (PCJda54a286946142d3_BranchPhases.body_injective sources p k r scratch) _ _ i

/-! ## 4. The three phase witnesses -/

/-- **The moment/clause `PhaseWitness`** from its loop, started at `laterA0` with the entry heads. -/
def laterW {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den k r scratch n : Nat} {x : BitInput n} {bits : List Bool}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {mode : Bool} {ph : Phase} {hin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → Nat} {tin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool} {fuel width : Nat}
    {code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}
    (hph : ph = .moment ∨ ph = .clause)
    (S : CloseoutFinalC10ModeNativeSchedule.Selection sources p k) (hn : S.onset ≤ n) (hr : r = S.exponent)
    (hm : mode = CloseoutWitness.BoundedFields.symmetric bits)
    (hI : LaterIn sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) mode ph (C10PartsSchedule.entryWidthSchedule sources k r n) hin tin)
    (L : ClauseLoop mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site mode ph (C10PartsSchedule.entryWidthSchedule sources k r n) code)
    (hA0 : L.A 0 = laterA0 sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) mode tin)
    (hH0 : L.H 0 = fun i => hin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch i))
    (liveScale : Nat) (hL : ∀ c, (L.values c).L = liveScale) (hT : ∀ c, (L.values c).target = (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)))
    (cost : Nat)
    (hcost : 4*NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)+PCPPQueryCachedBounds.callBudget (CloseoutLanguage.selectedPCPP sources)
      ((req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).circuit.size+(req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity)+L.siteFuel+21 ≤ cost)
    (hfuel : fuel = (2*capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)+4)+1+(NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)*(cost+3)+3+1+
      CloseoutFinalC10RetainedPhaseFold.fuel (C10PartsSchedule.entryWidthSchedule sources k r n) L.entries.length))
    (hwidth : width = CloseoutFinalC10WorkerFold.foldWidth (CompetitorRationalDecision.width (C10PartsSchedule.entryWidthSchedule sources k r n)) L.entries) :
    PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits
      site mode ph hin tin fuel width code :=
  have F := later_facts sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) mode ph (C10PartsSchedule.entryWidthSchedule sources k r n) hin tin hI
  PhaseWitness.ofLoop L liveScale (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (CloseoutFinalC10StageFields.stageLimits sources p)
    (CloseoutFinalC10ModeNativeEnvelope.nativeDenBits sources k p n)
    (loopOrder L) (loop_horder L) (loop_hmode L hm) (loop_hrecords L liveScale (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) hL hT)
    (phase_hmass sources p k den (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits ph)
    (by rw [hr]; exact phase_hcoeff sources p k den S hn x bits ph)
    (phase_htarget sources p ph) (phase_htargetpos sources p)
    (loop_hden L hm liveScale) (by rw [hr]; exact phase_hdenwidth sources p k S hn)
    (2*capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)+4) hin (laterMiddle sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) mode tin)
    (later_entry sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) mode ph hph hin tin hI.cache hI.cacheH)
    (fun i => by rw [hH0]) (fun i => by rw [hA0]; exact later_tape sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) mode tin i)
    hI.driverH (later_word sources p k r scratch (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) mode tin _ hI.driverT)
    (by rw [hA0]; exact F.1) (by rw [hA0]; exact F.2.1) (by rw [hA0]; exact F.2.2.1) (by rw [hA0]; exact F.2.2.2.1)
    (by rw [hA0]; exact F.2.2.2.2.1) (by rw [hA0]; exact F.2.2.2.2.2.1) (by rw [hA0]; exact F.2.2.2.2.2.2.1)
    (by rw [hH0]; exact hI.cacheH) (by rw [hH0]; exact hI.termH) (by rw [hA0]; exact F.2.2.2.2.2.2.2.1)
    (by rw [hA0]; exact F.2.2.2.2.2.2.2.2) (by rw [hH0]; exact hI.Hw) (by rw [hH0]; exact hI.Hf)
    cost hcost hfuel hwidth

/-- **The penalty `PhaseWitness`** from its loop, started at `penaltyA0` with the heads `S.heads`. -/
def penaltyW {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den : Nat} {hden : 0 < den} {k r scratch n : Nat} {x : BitInput n} {bits : List Bool}
    {hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {fuel width : Nat}
    {code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch .penalty}
    (S : CloseoutFinalC10ModeNativeSchedule.Selection sources p k) (hn : S.onset ≤ n) (hr : r = S.exponent)
    (L : ClauseLoop mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site
      (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty (C10PartsSchedule.entryWidthSchedule sources k r n) code)
    (hA0 : L.A 0 = penaltyA0 sources p den hden k r scratch n x bits hp)
    (hH0 : L.H 0 = fun j => (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j))
    (liveScale : Nat) (hL : ∀ c, (L.values c).L = liveScale) (hT : ∀ c, (L.values c).target = (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)))
    (cost : Nat)
    (hcost : 4*NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)+PCPPQueryCachedBounds.callBudget (CloseoutLanguage.selectedPCPP sources)
      ((req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).circuit.size+(req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity)+L.siteFuel+21 ≤ cost)
    (hfuel : fuel = (4*(C10PartsSchedule.entryWidthSchedule sources k r n)+23)+1+(NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)*(cost+3)+3+1+
      CloseoutFinalC10RetainedPhaseFold.fuel (C10PartsSchedule.entryWidthSchedule sources k r n) L.entries.length))
    (hwidth : width = CloseoutFinalC10WorkerFold.foldWidth (CompetitorRationalDecision.width (C10PartsSchedule.entryWidthSchedule sources k r n)) L.entries) :
    PhaseWitness mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits
      site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp) fuel width code :=
  have F := penalty_start sources p den hden k r scratch n x bits hp
  have hm := (penalty_bank sources p den hden k r scratch n x bits hp).1
  PhaseWitness.ofLoop L liveScale (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (CloseoutFinalC10StageFields.stageLimits sources p)
    (CloseoutFinalC10ModeNativeEnvelope.nativeDenBits sources k p n)
    (loopOrder L) (loop_horder L) (loop_hmode L hm) (loop_hrecords L liveScale (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) hL hT)
    (phase_hmass sources p k den (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits .penalty)
    (by rw [hr]; exact phase_hcoeff sources p k den S hn x bits .penalty)
    (phase_htarget sources p .penalty) (phase_htargetpos sources p)
    (loop_hden L hm liveScale) (by rw [hr]; exact phase_hdenwidth sources p k S hn)
    (4*(C10PartsSchedule.entryWidthSchedule sources k r n)+23) (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (penaltyMiddle sources p den hden k r scratch n x bits hp)
    (penalty_entry sources p den hden k r scratch n x bits hp (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp))
    (fun i => by rw [hH0]) (fun i => by rw [hA0]; exact penalty_tape sources p den hden k r scratch n x bits hp i)
    F.2.2.2.2.2.2.2.2.2.2.2.2.2.1 F.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    (by rw [hA0]; exact F.1) (by rw [hA0]; exact F.2.1) (by rw [hA0]; exact F.2.2.1) (by rw [hA0]; exact F.2.2.2.1)
    (by rw [hA0]; exact F.2.2.2.2.1) (by rw [hA0]; exact F.2.2.2.2.2.1) (by rw [hA0]; exact F.2.2.2.2.2.2.1)
    (by rw [hH0]; exact F.2.2.2.2.2.2.2.1) (by rw [hH0]; exact F.2.2.2.2.2.2.2.2.1)
    (by rw [hA0]; exact F.2.2.2.2.2.2.2.2.2.1) (by rw [hA0]; exact F.2.2.2.2.2.2.2.2.2.2.1)
    (by rw [hH0]; exact F.2.2.2.2.2.2.2.2.2.2.2.1) (by rw [hH0]; exact F.2.2.2.2.2.2.2.2.2.2.2.2.1)
    cost hcost hfuel hwidth

end
end NearCubicWires.SourcePhase
end

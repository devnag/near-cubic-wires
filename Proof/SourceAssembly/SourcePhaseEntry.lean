import Proof.SourceAssembly.SourcePhaseLoop

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

/-! ## 1. The explicit entry bank on the selected body (generic in `t P extra`) -/

section generic
variable {t P extra : Nat} (ht : 2 ≤ t) (hP : 302 ≤ P) (hsp : P+1155 ≤ extra)

/-- A low body tape `2 ≤ j < 278`, `j ≠ 216`, is the prologue's own port `j`. -/
theorem body_low (j : Fin (t+2+extra-4)) (h2 : 2 ≤ j.val) (h278 : j.val < 278) (h216 : j.val ≠ 216) :
    (ControllerSelectedLayout.body ht hP hsp j).val = t+2+j.val := by
  simp only [ControllerSelectedLayout.body, ControllerSelectedLayout.location]
  split_ifs <;> omega

/-- A high body tape `offset ≤ j`, `j ≠ offset+51`, sits at `j+4`. -/
theorem body_high (j : Fin (t+2+extra-4)) (hj : P+t-2 ≤ j.val) (h51 : j.val ≠ P+t-2+51) :
    (ControllerSelectedLayout.body ht hP hsp j).val = j.val+4 := by
  simp only [ControllerSelectedLayout.body, ControllerSelectedLayout.location]
  split_ifs <;> omega

variable (hfit : P ≤ extra) (hP219 : 219 ≤ P) (h96 : P+96 ≤ extra) (C : Fin 19 → Fin t)
  (A : Fin t → List Bool) (L : Nat) (o1 : Fin P → List Bool) (o2 : Fin 116 → List Bool)

/-- (G1) Low body tapes carry the prologue output. -/
theorem bank_low (j : Fin (t+2+extra-4)) (h2 : 2 ≤ j.val) (h278 : j.val < 278) (h216 : j.val ≠ 216)
    (h218 : j.val ≠ 218) :
    install (WorkspaceSelectedEntryInit.ports P hP219 h96 C)
      (install (WorkspaceSelectedEntry.slots ht hfit) (WorkspaceSelectedProgram.finalBank A L extra) o1) o2
      (ControllerSelectedLayout.body ht hP hsp j) = o1 ⟨j.val, by omega⟩ := by
  have hb := body_low ht hP hsp j h2 h278 h216
  rw [install_other _ _ _ _ (by
    intro i he
    have hv := congrArg Fin.val he
    have hi := i.isLt
    rw [hb] at hv
    by_cases hc : i.val < 19
    · have hC := (C ⟨i.val, hc⟩).isLt
      simp only [WorkspaceSelectedEntryInit.ports, dif_pos hc, Fin.val_castAdd] at hv
      omega
    · simp only [WorkspaceSelectedEntryInit.ports, dif_neg hc] at hv
      split_ifs at hv <;> omega)]
  have he : ControllerSelectedLayout.body ht hP hsp j =
      WorkspaceSelectedEntry.slots ht hfit ⟨j.val, by omega⟩ := by
    apply Fin.ext
    rw [hb]
    simp only [WorkspaceSelectedEntry.slots]
    split_ifs <;> omega
  rw [he, install_slot _ (WorkspaceSelectedEntry.slots_injective ht hfit)]

/-- (G2) Body tape 218 is the initializer's port 19 (the width driver). -/
theorem bank_218 (hC : Function.Injective C) :
    install (WorkspaceSelectedEntryInit.ports P hP219 h96 C)
      (install (WorkspaceSelectedEntry.slots ht hfit) (WorkspaceSelectedProgram.finalBank A L extra) o1) o2
      (ControllerSelectedLayout.body ht hP hsp ⟨218, by omega⟩) = o2 19 := by
  have hb := body_low ht hP hsp ⟨218, by omega⟩ (by show 2 ≤ 218; omega) (by show 218 < 278; omega) (by show 218 ≠ 216; omega)
  have he : ControllerSelectedLayout.body ht hP hsp ⟨218, by omega⟩ =
      WorkspaceSelectedEntryInit.ports P hP219 h96 C 19 := by
    apply Fin.ext
    rw [hb]
    simp [WorkspaceSelectedEntryInit.ports]
  rw [he, install_slot _ (WorkspaceSelectedEntryInit.ports_injective P hP219 h96 C hC)]

/-- A tape at or beyond the fresh region start `t+2` that neither map touches reads blank. -/
theorem bank_fresh (v : Fin (t+1+1+extra)) (hv : t+2 ≤ v.val)
    (hs : ∀ i, WorkspaceSelectedEntry.slots ht hfit i ≠ v)
    (hq : ∀ i, WorkspaceSelectedEntryInit.ports P hP219 h96 C i ≠ v) :
    install (WorkspaceSelectedEntryInit.ports P hP219 h96 C)
      (install (WorkspaceSelectedEntry.slots ht hfit) (WorkspaceSelectedProgram.finalBank A L extra) o1) o2
      v = [] := by
  rw [install_other _ _ _ _ hq, install_other _ _ _ _ hs]
  have he : v = (⟨v.val-(t+2), by have := v.isLt; omega⟩ : Fin extra).natAdd (t+1+1) := by
    apply Fin.ext
    simp only [Fin.val_natAdd]
    omega
  rw [he]
  exact Fin.addCases_right _

/-- (G3) High body tapes `offset ≤ j < offset+96`, `j ≠ offset+51`, carry the initializer's fresh
ports `20 + (j - offset)`. -/
theorem bank_high (j : Fin (t+2+extra-4)) (hj : P+t-2 ≤ j.val) (hj96 : j.val < P+t-2+96)
    (h51 : j.val ≠ P+t-2+51) (hC : Function.Injective C) :
    install (WorkspaceSelectedEntryInit.ports P hP219 h96 C)
      (install (WorkspaceSelectedEntry.slots ht hfit) (WorkspaceSelectedProgram.finalBank A L extra) o1) o2
      (ControllerSelectedLayout.body ht hP hsp j) = o2 ⟨20+(j.val-(P+t-2)), by omega⟩ := by
  have hb := body_high ht hP hsp j hj h51
  have he : ControllerSelectedLayout.body ht hP hsp j =
      WorkspaceSelectedEntryInit.ports P hP219 h96 C ⟨20+(j.val-(P+t-2)), by omega⟩ := by
    apply Fin.ext
    rw [hb]
    simp only [WorkspaceSelectedEntryInit.ports, show ¬(20+(j.val-(P+t-2)) < 19) by omega, dif_neg,
      not_false_eq_true, Fin.val_mk]
    split_ifs <;> omega
  rw [he, install_slot _ (WorkspaceSelectedEntryInit.ports_injective P hP219 h96 C hC)]

/-- (G4) Body tapes from `offset+96` on read blank. -/
theorem bank_far (j : Fin (t+2+extra-4)) (hj : P+t-2+96 ≤ j.val) :
    install (WorkspaceSelectedEntryInit.ports P hP219 h96 C)
      (install (WorkspaceSelectedEntry.slots ht hfit) (WorkspaceSelectedProgram.finalBank A L extra) o1) o2
      (ControllerSelectedLayout.body ht hP hsp j) = [] := by
  have hb := body_high ht hP hsp j (by omega) (by omega)
  apply bank_fresh ht hfit hP219 h96 C A L o1 o2 _ (by omega)
  · intro i he
    have hv := congrArg Fin.val he
    have hi := i.isLt
    rw [hb] at hv
    simp only [WorkspaceSelectedEntry.slots] at hv
    split_ifs at hv <;> omega
  · intro i he
    have hv := congrArg Fin.val he
    have hi := i.isLt
    rw [hb] at hv
    by_cases hc : i.val < 19
    · have hC := (C ⟨i.val, hc⟩).isLt
      simp only [WorkspaceSelectedEntryInit.ports, dif_pos hc, Fin.val_castAdd] at hv
      omega
    · simp only [WorkspaceSelectedEntryInit.ports, dif_neg hc] at hv
      split_ifs at hv <;> omega

/-- The original tape `c` is the body tape `c` (if `c < 2`) or `P+c-2`. -/
theorem body_original (c : Fin t) :
    ControllerSelectedLayout.body ht hP hsp
        ⟨if c.val < 2 then c.val else P+c.val-2, by have := c.isLt; split_ifs <;> omega⟩ =
      ((c.castAdd 1).castAdd 1).castAdd extra := by
  apply Fin.ext
  simp only [ControllerSelectedLayout.body, Fin.val_castAdd]
  exact (ControllerSelectedLayout.facts t P extra ht hP hsp).2.2.2.2.1 c.val c.isLt

/-- (G5) The retained original cache carries the initializer's cache ports. -/
theorem bank_cache (hC : Function.Injective C) (i : Fin 19) :
    install (WorkspaceSelectedEntryInit.ports P hP219 h96 C)
      (install (WorkspaceSelectedEntry.slots ht hfit) (WorkspaceSelectedProgram.finalBank A L extra) o1) o2
      (((C i).castAdd 1).castAdd 1 |>.castAdd extra) = o2 (i.castAdd 97) := by
  have he : (((C i).castAdd 1).castAdd 1 |>.castAdd extra) =
      WorkspaceSelectedEntryInit.ports P hP219 h96 C (i.castAdd 97) := by
    simp only [WorkspaceSelectedEntryInit.ports, Fin.val_castAdd, dif_pos i.isLt]
  rw [he, install_slot _ (WorkspaceSelectedEntryInit.ports_injective P hP219 h96 C hC)]

/-- Prologue heads on the body: 0 except at the prologue's own last port `P-1`. -/
theorem heads_body (oh : Fin P → Nat) (hoh : ∀ i : Fin P, i.val ≠ P-1 → oh i = 0)
    (j : Fin (t+2+extra-4)) (hj : j.val ≠ P-1) :
    dockH (WorkspaceSelectedEntry.slots ht hfit) (fun _ => 0) oh (ControllerSelectedLayout.body ht hP hsp j) = 0 := by
  by_cases h : ∃ i, WorkspaceSelectedEntry.slots ht hfit i = ControllerSelectedLayout.body ht hP hsp j
  · obtain ⟨i, hi⟩ := h
    rw [← hi, dockH_slot _ (WorkspaceSelectedEntry.slots_injective ht hfit)]
    apply hoh
    intro hl
    have hv := congrArg Fin.val hi
    have hjl := j.isLt
    simp only [WorkspaceSelectedEntry.slots, ControllerSelectedLayout.body,
      ControllerSelectedLayout.location] at hv
    split_ifs at hv <;> omega
  · exact dockH_other _ _ _ _ (fun i he => h ⟨i, he⟩)

end generic

/-- The prologue output below its last port is the supplier-call bank. -/
theorem output_low (sources : EightSources) (k r D n : Nat) (x bits : List Bool) (w : Nat → List Bool)
    (i : Fin (WorkspaceSelectedEntry.size sources k r D)) (hi : i.val < 278) :
    WorkspaceSelectedEntry.output sources k r D n x bits w i =
      C10SupplierCall.bankAt [] (CompareMachine.word 0)
        (List.replicate (C10PartsSchedule.entryWidthSchedule sources k r n) true) x bits w i.val := by
  let b := 218+(60+(WorkspaceSelectedEntry.engineTapes sources k r D+23))
  have hb : i.val < b := by dsimp only [b]; omega
  let j : Fin b := ⟨i.val, hb⟩
  have he : i = j.castAdd 1 := Fin.ext rfl
  rw [he]
  simp only [WorkspaceSelectedEntry.output, Fin.addCases_left, C10SupplierCall.bank, Fin.val_castAdd]

/-- The prologue exit heads are 0 below its last port. -/
theorem outputHeads_low (sources : EightSources) (k r D : Nat)
    (i : Fin (WorkspaceSelectedEntry.size sources k r D)) (hi : i.val ≠ WorkspaceSelectedEntry.size sources k r D - 1) :
    WorkspaceSelectedEntry.outputHeads sources k r D i = 0 := by
  let b := 218+(60+(WorkspaceSelectedEntry.engineTapes sources k r D+23))
  have hb : i.val < b := by
    have := i.isLt
    simp only [WorkspaceSelectedEntry.size] at this hi
    dsimp only [b]; omega
  let j : Fin b := ⟨i.val, hb⟩
  have he : i = j.castAdd 1 := Fin.ext rfl
  rw [he]
  simp only [WorkspaceSelectedEntry.outputHeads, Fin.addCases_left]

/-! ## 2. Row C1: `S.bank` is the explicit installed entry bank -/

/-- A low body index (below `1455 ≤ offset+1154`). -/
def lowIdx (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k r scratch : Nat)
    (m : Nat) (hm : m < 1455) : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) :=
  ⟨m, by have := PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch
         have := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
         omega⟩

section requestEq
open NearCubicWires.RepairOrdinary.CloseoutWitness NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedSource
  NearCubicWires.RepairSource.SelectedRecoveryIntegration NearCubicWires.CanonicalWitnessCodec
open private decode_cast size_cast from Proof.CaseAnalysis.WitnessDyadicGuards

theorem request_eq_total' (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n ^ (k + 2))) (G : Nat) {n : Nat}
    (x : BitInput n) (bits : List Bool)
    (oracle : BooleanCircuit (SelectedOracle.width (fixedProjection sources) k
      (hierarchy sources k clock).coefficient (padding sources k clock)
      (code sources k clock) (List.ofFn x)))
    (hdecode : decodeBooleanCircuit _ (RadixSemantics.value (BoundedFields.oracle bits)) = some oracle)
    (hsize : oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound G
      (SelectedOracle.width (fixedProjection sources) k (hierarchy sources k clock).coefficient
        (padding sources k clock) (code sources k clock) (List.ofFn x))) :
    ColdNative.request (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources) k
      (hierarchy sources k clock).coefficient (padding sources k clock) (code sources k clock)
      x (Nat.le_max_right _ _) oracle =
      CloseoutFinal.req sources k clock x (CloseoutFinal.C10TotalDecode.oracleOf sources k clock G n bits) := by
  let hw := width sources k clock x
  let selectedOracle := cast (congrArg BooleanCircuit hw) oracle
  have hcast : cast (congrArg BooleanCircuit hw.symm) selectedOracle = oracle := by
    exact (cast_cast (congrArg BooleanCircuit hw) (congrArg BooleanCircuit hw.symm) oracle).trans
      (cast_eq _ oracle)
  have decoded : decodeBooleanCircuit _ (RadixSemantics.value (BoundedFields.oracle bits)) =
      some selectedOracle := decode_cast hw.symm hdecode
  have sized : selectedOracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound G
      ((outer sources k clock).result.pcp.nativeWidth n) := by
    have h := size_cast hw.symm oracle
    change selectedOracle.size = oracle.size at h
    exact h.le.trans (hsize.trans (congrArg (RecoveryScheduleEnvelope.oracleSizeBound G) hw).le)
  have pinned := CloseoutFinal.C10TotalDecode.oracleOf_pin sources k clock G n bits
    selectedOracle decoded sized
  have same := request_eq sources k clock x selectedOracle
  have physical := congrArg (ColdNative.request (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
    k (hierarchy sources k clock).coefficient (padding sources k clock) (code sources k clock)
    x (Nat.le_max_right _ _)) hcast
  exact (physical.symm.trans same).trans (congrArg (CloseoutFinal.req sources k clock x) pinned.symm)

end requestEq

section entry
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
  (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
  (hp : P1Independent.CappedLegalAdmission.passed sources p
    (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
    (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)

attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size
open NearCubicWires.RepairOrdinary.CloseoutWitness NearCubicWires.RepairSource.SelectedRecoveryIntegration
  NearCubicWires.CanonicalWitnessCodec

theorem size_302 : 302 ≤ WorkspaceSelectedEntry.size sources k r p.clauseDegree := by
  unfold WorkspaceSelectedEntry.size; omega

theorem size_fit : WorkspaceSelectedEntry.size sources k r p.clauseDegree ≤
    ControllerSelectedContinuation.extra sources p k r scratch :=
  (Nat.le_add_right _ _).trans (PCJ687b3b71abe848ce_.space sources p k r scratch)

theorem ready_installed :
    let source := fixedProjection sources
    let a := CloseoutLanguage.selectedPCPP sources
    let CH := (SelectedSource.hierarchy sources k (PolynomialClock.ordinaryClock k)).coefficient
    let Cpad := padding sources k (PolynomialClock.ordinaryClock k)
    let code := SelectedSource.code sources k (PolynomialClock.ordinaryClock k)
    ∃ (A : Fin (WorkspaceSelectedAdmission.originalTapes sources p k) → List Bool) (L : Nat)
      (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)))
      (w : Nat → List Bool) (out : Fin 116 → List Bool),
      decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x))
        (RadixSemantics.value (BoundedFields.oracle bits)) = some oracle ∧
      oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound p.degree
        (SelectedOracle.width source k CH Cpad code (List.ofFn x)) ∧
      WorkspaceSelectedOriginals.Originals sources p k x bits A ∧
      (∀ j, A (WorkspaceSelectedEntryReady.cache sources p k (BoundedFields.symmetric bits) j) =
        WorkspaceSelectedEntryCount.cacheData a (ColdNative.request source a k CH Cpad code x (Nat.le_max_right _ _) oracle) j) ∧
      PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp =
        install (WorkspaceSelectedEntryInit.ports (WorkspaceSelectedEntry.size sources k r p.clauseDegree)
            (by have := size_302 sources p k r; omega) (PCJ687b3b71abe848ce_.space sources p k r scratch)
            (WorkspaceSelectedEntryReady.cache sources p k (BoundedFields.symmetric bits)))
          (install (WorkspaceSelectedEntry.slots (WorkspaceSelectedEntryReady.old_size sources p k)
              (size_fit sources p k r scratch))
            (WorkspaceSelectedProgram.finalBank A L (ControllerSelectedContinuation.extra sources p k r scratch))
            (WorkspaceSelectedEntry.output sources k r p.clauseDegree n (List.ofFn x) bits w)) out ∧
      out (WorkspaceSelectedEntryCount.count 72) =
        List.replicate (2^(a.output (ColdNative.request source a k CH Cpad code x (Nat.le_max_right _ _) oracle)).clauseBits) true ∧
      out (WorkspaceSelectedEntryCount.append 0) =
        List.replicate (C10PartsSchedule.entryWidthSchedule sources k r n) true ∧
      out (WorkspaceSelectedEntryCount.cache 0) = out (WorkspaceSelectedEntryCount.cache 0) ∧
      (∀ j, out (WorkspaceSelectedEntryCount.cache j) =
        WorkspaceSelectedEntryCount.cacheData a (ColdNative.request source a k CH Cpad code x (Nat.le_max_right _ _) oracle) j) ∧
      PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp
          (PCJda54a286946142d3_BranchPhases.driver sources p k r scratch) =
        UnaryTemplate.tape (2^(a.output (ColdNative.request source a k CH Cpad code x (Nat.le_max_right _ _) oracle)).clauseBits) := by
  intro source a CH Cpad code
  let receipt := ControllerCappedSelected.selected_run sources p den hden k
    (PolynomialClock.ordinaryClock k) (ControllerSelectedContinuation.extra sources p k r scratch) n x bits
  have hr := receipt.choose_spec.choose_spec.1
  have ho := PCJ138fdb4302e34c7e_CappedOriginals.originals_of_run
    sources gamma p den hden k (PolynomialClock.ordinaryClock k) _ n x bits _ _ hr hp
  have hc := receipt.choose_spec.choose_spec.2.2.1 hp
  obtain ⟨oracle, hdecode, hsize, w, out, run, hdrv, hcache, _h28, h72, h0, _rest⟩ :=
    PCJ57feb257fbc0439a_.run_from_facts sources gamma p k r _ (PCJ687b3b71abe848ce_.space sources p k r scratch)
      n x bits _ _ ho hc
  obtain ⟨_H, oracle', hdecode', _hsize', fields⟩ := hc
  have same : oracle' = oracle := Option.some.inj (hdecode'.symm.trans hdecode)
  subst same
  have actual := run.enlarge
    (PCJ687b3b71abe848ce_.actual_fuel_le sources p den hden k r n x bits oracle' hp hsize)
  have eq := NearCubicWires.SourceParent.exit_unique
    (PCJ687b3b71abe848ce_.ready_step sources p den hden k r _ (PCJ687b3b71abe848ce_.space sources p k r scratch)
      n x bits hp) actual
  have hC := PCJ30aa6f1b7c2a4221_.Selected.original_cache_injective sources p k (BoundedFields.symmetric bits)
  have hinj := WorkspaceSelectedEntryInit.ports_injective (WorkspaceSelectedEntry.size sources k r p.clauseDegree)
    (by have := size_302 sources p k r; omega) (PCJ687b3b71abe848ce_.space sources p k r scratch)
    (WorkspaceSelectedEntryReady.cache sources p k (BoundedFields.symmetric bits)) hC
  refine ⟨_, _, oracle', w, out, hdecode, hsize, ho, fun j => (fields j).1, eq.2, h72, h0, rfl,
    fun j => ?_, ?_⟩
  · exact (install_slot _ hinj _ _ _).symm.trans (hcache j)
  · change PCJ687b3b71abe848ce_.readyBank sources p den hden k r _ (PCJ687b3b71abe848ce_.space sources p k r scratch)
      n x bits hp _ = _
    rw [eq.2]
    exact hdrv

/-- **C1, on the body.** Every fact about the penalty entry bank that the penalty entry, the loop
start and the cross-phase frames read: `S.mode = symmetric bits`; the blank low bank; the count word
on 90; the width driver `1^b` on 218; the clause counter `1^N` on `offset+53`; blank from
`offset+96` on; the query cache at `clauseData 0`; the clause driver `tape N`; zero heads away from
the prologue's last port; driver head 1. `N`/`CD` are at the consumer's own request
`req … (oracleOf … p.degree n bits)` (identified by `request_eq_total'`). -/
theorem penalty_bank :
    let clock := PolynomialClock.ordinaryClock k
    let oracle := C10TotalDecode.oracleOf sources k clock p.degree n bits
    let S := PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp
    let HS := PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch
    let body := PCJda54a286946142d3_BranchPhases.body sources p k r scratch
    PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp = BoundedFields.symmetric bits ∧
    (∀ j : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch),
      2 ≤ j.val → j.val < 278 → j.val ≠ 90 → j.val ≠ 216 → j.val ≠ 218 → S (body j) = []) ∧
    S (body (lowIdx sources p k r scratch 90 (by omega))) = CompareMachine.word 0 ∧
    S (body (lowIdx sources p k r scratch 218 (by omega))) =
      List.replicate (C10PartsSchedule.entryWidthSchedule sources k r n) true ∧
    S (body (PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch)) =
      List.replicate (NC sources k clock x oracle) true ∧
    (∀ j : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch),
      PCJda54a286946142d3_BranchPhases.offset sources p k r + 96 ≤ j.val → S (body j) = []) ∧
    (∀ i, S (body (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch
      (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i)) = CD sources k clock x oracle 0 i) ∧
    S (PCJda54a286946142d3_BranchPhases.driver sources p k r scratch) = UnaryTemplate.tape (NC sources k clock x oracle) ∧
    (∀ j : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch),
      j.val ≠ WorkspaceSelectedEntry.size sources k r p.clauseDegree - 1 → HS (body j) = 0) ∧
    HS (PCJda54a286946142d3_BranchPhases.driver sources p k r scratch) = 1 := by
  intro clock oracle S HS body
  obtain ⟨A, L, oracle0, w, out, hdecode, hsize, ho, hcA, hbank, h72, h0, -, hcache, hdrv⟩ :=
    ready_installed sources p den hden k r scratch n x bits hp
  have hreq := request_eq_total' sources k clock p.degree x bits oracle0 hdecode hsize
  rw [hreq] at h72 hcache hcA hdrv
  have ht := WorkspaceSelectedEntryReady.old_size sources p k
  have hP := size_302 sources p k r
  have hsp := PCJda54a286946142d3_BranchPhases.space sources p k r scratch
  have h96 := PCJ687b3b71abe848ce_.space sources p k r scratch
  have hfit := size_fit sources p k r scratch
  have hC := PCJ30aa6f1b7c2a4221_.Selected.original_cache_injective sources p k (BoundedFields.symmetric bits)
  have hoff : PCJda54a286946142d3_BranchPhases.offset sources p k r =
      WorkspaceSelectedEntry.size sources k r p.clauseDegree + WorkspaceSelectedAdmission.originalTapes sources p k - 2 := rfl
  have hbody : ∀ j, body j = ControllerSelectedLayout.body ht hP hsp j := fun j => rfl
  -- the mode
  have hmodeH : HS (WorkspaceSelectedEntryReady.modePort sources p k (ControllerSelectedContinuation.extra sources p k r scratch)) = 0 := by
    change WorkspaceSelectedEntryReady.finalHeads sources p k r _ h96 _ = 0
    unfold WorkspaceSelectedEntryReady.finalHeads
    rw [if_neg (by
      intro he
      have hv := congrArg Fin.val he
      simp only [WorkspaceSelectedEntryReady.modePort, WorkspaceSelectedEntryReady.driver, Fin.val_castAdd,
        WorkspaceSelectedOriginals.headerPort_val] at hv
      have := hP
      omega)]
    exact WorkspaceSelectedEntryInit.old_heads_zero sources k r p.clauseDegree _ _ ht hfit _
  have hpost : install (WorkspaceSelectedEntry.slots ht hfit)
      (WorkspaceSelectedProgram.finalBank A L (ControllerSelectedContinuation.extra sources p k r scratch))
      (WorkspaceSelectedEntry.output sources k r p.clauseDegree n (List.ofFn x) bits w)
      (WorkspaceSelectedEntryReady.modePort sources p k (ControllerSelectedContinuation.extra sources p k r scratch)) =
      [BoundedFields.symmetric bits] :=
    (WorkspaceSelectedEntryFacts.old_bank_retained sources k r p.clauseDegree n _ _ ht hfit A L (List.ofFn x)
      bits w ((congrArg A (Fin.ext (WorkspaceSelectedOriginals.headerPort_val sources p k 0).symm)).trans ho.1)
      ((congrArg A (Fin.ext (WorkspaceSelectedOriginals.headerPort_val sources p k 1).symm)).trans ho.2.1) _).trans ho.2.2
  have hmodeA : S (WorkspaceSelectedEntryReady.modePort sources p k (ControllerSelectedContinuation.extra sources p k r scratch)) =
      [BoundedFields.symmetric bits] := by
    change PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp _ = _
    rw [hbank]
    by_cases h : ∃ i, WorkspaceSelectedEntryInit.ports (WorkspaceSelectedEntry.size sources k r p.clauseDegree)
        (by omega) h96 (WorkspaceSelectedEntryReady.cache sources p k (BoundedFields.symmetric bits)) i =
        WorkspaceSelectedEntryReady.modePort sources p k (ControllerSelectedContinuation.extra sources p k r scratch)
    · obtain ⟨i, hi⟩ := h
      have hv := congrArg Fin.val hi
      by_cases hc : i.val < 19
      · have hCi : WorkspaceSelectedEntryReady.cache sources p k (BoundedFields.symmetric bits) ⟨i.val, hc⟩ =
            WorkspaceSelectedOriginals.headerPort sources p k 142 := by
          apply Fin.ext
          simp only [WorkspaceSelectedEntryInit.ports, dif_pos hc, Fin.val_castAdd,
            WorkspaceSelectedEntryReady.modePort] at hv
          exact hv
        rw [← hi, install_slot _ (WorkspaceSelectedEntryInit.ports_injective _ _ _ _ hC)]
        have hic : i = WorkspaceSelectedEntryCount.cache ⟨i.val, hc⟩ := Fin.ext rfl
        rw [hic, hcache, ← hcA, hCi]
        exact ho.2.2
      · have hlt := (WorkspaceSelectedOriginals.headerPort sources p k 142).isLt
        simp only [WorkspaceSelectedEntryInit.ports, dif_neg hc, WorkspaceSelectedEntryReady.modePort,
          Fin.val_castAdd, WorkspaceSelectedOriginals.headerPort_val] at hv
        split_ifs at hv <;> omega
    · rw [install_other _ _ _ _ (fun i he => h ⟨i, he⟩)]
      exact hpost
  have hmode : PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp =
      BoundedFields.symmetric bits := by
    change readTapeBit (S _) (HS _) = _
    rw [hmodeA, hmodeH]
    rfl
  refine ⟨hmode, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j h2 h278 h90 h216 h218
    change PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp _ = _
    rw [hbank, hbody, bank_low ht hP hsp hfit (by omega) h96 _ A L _ out j h2 h278 h216 h218,
      output_low _ _ _ _ _ _ _ _ _ h278]
    simp only [C10SupplierCall.bankAt]
    split_ifs <;> first | rfl | omega
  · change PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp _ = _
    rw [hbank, hbody, bank_low ht hP hsp hfit (by omega) h96 _ A L _ out _ (by show 2 ≤ 90; omega)
      (by show 90 < 278; omega) (by show 90 ≠ 216; omega) (by show 90 ≠ 218; omega),
      output_low _ _ _ _ _ _ _ _ _ (by show 90 < 278; omega)]
    rfl
  · change PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp _ = _
    rw [hbank, hbody]
    have e := bank_218 ht hP hsp hfit (by omega) h96 _ A L
      (WorkspaceSelectedEntry.output sources k r p.clauseDegree n (List.ofFn x) bits w) out hC
    exact e.trans h0
  · change PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp _ = _
    rw [hbank, hbody]
    have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
    have e := bank_high ht hP hsp hfit (by omega) h96 _ A L
      (WorkspaceSelectedEntry.output sources k r p.clauseDegree n (List.ofFn x) bits w) out
      (PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch)
      (by simp only [PCJ30aa6f1b7c2a4221_.Selected.terminal]; omega)
      (by simp only [PCJ30aa6f1b7c2a4221_.Selected.terminal]; omega)
      (by simp only [PCJ30aa6f1b7c2a4221_.Selected.terminal]; omega) hC
    rw [e]
    have hidx : (⟨20+((PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch).val -
        (WorkspaceSelectedEntry.size sources k r p.clauseDegree + WorkspaceSelectedAdmission.originalTapes sources p k - 2)),
        by simp only [PCJ30aa6f1b7c2a4221_.Selected.terminal]; omega⟩ : Fin 116) = WorkspaceSelectedEntryCount.count 72 := by
      have h73 : (WorkspaceSelectedEntryCount.count 72).val = 73 := rfl
      apply Fin.ext
      rw [h73]
      simp only [PCJ30aa6f1b7c2a4221_.Selected.terminal]
      omega
    rw [hidx]
    exact h72
  · intro j hj
    change PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp _ = _
    rw [hbank, hbody]
    exact bank_far ht hP hsp hfit (by omega) h96 _ A L _ out j (by omega)
  · intro i
    rw [hmode]
    change PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp _ = _
    rw [hbank, hbody]
    have hb := body_original ht hP hsp (WorkspaceSelectedEntryReady.cache sources p k (BoundedFields.symmetric bits) i)
    have he : ControllerSelectedLayout.body ht hP hsp
        (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (BoundedFields.symmetric bits) i) =
        ControllerSelectedLayout.body ht hP hsp
          ⟨if (WorkspaceSelectedEntryReady.cache sources p k (BoundedFields.symmetric bits) i).val < 2 then
            (WorkspaceSelectedEntryReady.cache sources p k (BoundedFields.symmetric bits) i).val else
            WorkspaceSelectedEntry.size sources k r p.clauseDegree +
              (WorkspaceSelectedEntryReady.cache sources p k (BoundedFields.symmetric bits) i).val - 2,
            by have := (WorkspaceSelectedEntryReady.cache sources p k (BoundedFields.symmetric bits) i).isLt
               split_ifs <;> omega⟩ := rfl
    rw [he, hb, bank_cache ht hfit (by omega) h96 _ A L _ out hC i]
    exact hcache i
  · exact hdrv
  · intro j hj
    change WorkspaceSelectedEntryReady.finalHeads sources p k r _ h96 _ = 0
    unfold WorkspaceSelectedEntryReady.finalHeads
    split_ifs with hdr
    · exact absurd hdr (PCJda54a286946142d3_BranchPhases.body_ne_driver sources p k r scratch j)
    exact heads_body ht hP hsp hfit (WorkspaceSelectedEntry.outputHeads sources k r p.clauseDegree)
      (outputHeads_low sources k r p.clauseDegree) j hj
  · exact WorkspaceSelectedEntryReady.driver_head sources p k r _ h96

/-! ## 3. Row C2: the penalty entry (`FirstPhaseEntry`, docked) and the penalty loop start -/

/-- FirstPhaseEntry's local exit; it depends on the width `b` only. -/
def firstLocal (b : Nat) : Fin 10 → List Bool :=
  Classical.choose (CloseoutFinalC10FirstPhaseEntry.local_run b)

theorem firstLocal_spec (b : Nat) :
    Step CloseoutFinalC10FirstPhaseEntry.localMachine (4*b+23) (fun _ => 0)
        (CloseoutFinalC10FirstPhaseEntry.input b) (fun _ => 0) (firstLocal b) ∧
      firstLocal b 0 = List.replicate b true ∧ firstLocal b 1 = [] ∧
      firstLocal b 2 = List.replicate b true ∧ firstLocal b 4 = List.replicate b true ∧
      firstLocal b 6 = [false] ∧ firstLocal b 8 = [false] :=
  Classical.choose_spec (CloseoutFinalC10FirstPhaseEntry.local_run b)

theorem space1095 : PCJda54a286946142d3_BranchPhases.offset sources p k r + 1095 <
    ControllerSelectedContinuation.bodyTapes sources p k r scratch := by
  have := PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch; omega

/-- The first-entry slots on the body. -/
abbrev fSlots := CloseoutFinalC10FirstPhaseEntry.firstSlots (PCJda54a286946142d3_BranchPhases.offset sources p k r)
  (ControllerSelectedContinuation.bodyTapes sources p k r scratch)
  (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r) (space1095 sources p k r scratch)

/-- **The penalty loop-start bank** `A 0` (row E7's choice `A 0 := middle ∘ body`). -/
def penaltyA0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool :=
  install (fSlots sources p k r scratch)
    (fun j => PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp
      (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j))
    (firstLocal (C10PartsSchedule.entryWidthSchedule sources k r n))

/-- **The penalty middle bank** (the entry's exit, `hentry`'s `middle`). -/
def penaltyMiddle : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool :=
  install (PCJda54a286946142d3_BranchPhases.body sources p k r scratch)
    (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp)
    (penaltyA0 sources p den hden k r scratch n x bits hp)

/-- The first-entry slots never hit the prologue's last port `P-1`. -/
theorem fSlots_val (i : Fin 10) :
    (fSlots sources p k r scratch i).val = 218 ∨
      PCJda54a286946142d3_BranchPhases.offset sources p k r + 124 ≤ (fSlots sources p k r scratch i).val := by
  fin_cases i <;> simp [fSlots, CloseoutFinalC10FirstPhaseEntry.firstSlots]

/-- **C2 (`hentry`).** The fixed penalty phase entry runs from the chosen entry bank `S.bank`, at the
accepted fuel `4*b+23`, heads unchanged, to `penaltyMiddle`. -/
theorem penalty_entry (mode : Bool) :
    Step (RecoveryFocus.machine (PCJda54a286946142d3_BranchPhases.body sources p k r scratch)
        (PCJda54a286946142d3_BranchPhases.phaseEntry sources p k r scratch mode .penalty).2)
      (4*C10PartsSchedule.entryWidthSchedule sources k r n+23)
      (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch)
      (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp)
      (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch)
      (penaltyMiddle sources p den hden k r scratch n x bits hp) := by
  obtain ⟨_hmode, hlow, _h90, h218, _hterm, hfar, _hcache, _hdrv, hheads, _hdh⟩ :=
    penalty_bank sources p den hden k r scratch n x bits hp
  have hP := size_302 sources p k r
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have hoff : PCJda54a286946142d3_BranchPhases.offset sources p k r =
      WorkspaceSelectedEntry.size sources k r p.clauseDegree + WorkspaceSelectedAdmission.originalTapes sources p k - 2 := rfl
  have ht := WorkspaceSelectedEntryReady.old_size sources p k
  have spec := firstLocal_spec (C10PartsSchedule.entryWidthSchedule sources k r n)
  have hH : ∀ j, PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch
      (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (fSlots sources p k r scratch j)) = 0 := by
    intro j
    apply hheads
    rcases fSlots_val sources p k r scratch j with h | h <;> omega
  have hA : ∀ j, PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp
      (PCJda54a286946142d3_BranchPhases.body sources p k r scratch (fSlots sources p k r scratch j)) =
      CloseoutFinalC10FirstPhaseEntry.input (C10PartsSchedule.entryWidthSchedule sources k r n) j := by
    intro j
    fin_cases j
    · exact h218
    all_goals
      apply hfar
      simp [fSlots, CloseoutFinalC10FirstPhaseEntry.firstSlots]
  have inner := (spec.1.dock (fSlots sources p k r scratch)
    (CloseoutFinalC10FirstPhaseEntry.slots_injective _ _ _ _)
    (fun j => PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j))
    (fun j => PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp
      (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j)) hH hA).congr
    (dockH_existing _ _ _ hH) rfl
  have outer := (inner.dock (PCJda54a286946142d3_BranchPhases.body sources p k r scratch)
    (PCJda54a286946142d3_BranchPhases.body_injective sources p k r scratch)
    (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch)
    (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp) (fun _ => rfl) (fun _ => rfl)).congr
    (dockH_existing _ _ _ (fun _ => rfl)) rfl
  exact outer

/-- The penalty word slots, as numbers. -/
theorem wd_penalty_val (i : Fin 278) :
    (Wd sources p k r scratch .penalty i).val =
      if i.val = 274 then PCJda54a286946142d3_BranchPhases.offset sources p k r + 126
      else if i.val = 275 then PCJda54a286946142d3_BranchPhases.offset sources p k r + 127 else i.val := by
  have hw0 : (C10TailSlotsUniform.widthSlotT .penalty 0).val = 2 := rfl
  have hw1 : (C10TailSlotsUniform.widthSlotT .penalty 1).val = 3 := rfl
  simp only [Wd, CloseoutFinalC10RetainedPhaseFold.wordSlots, CloseoutFinalC10RetainedPhaseFold.tailSlots,
    CloseoutFinalC10RetainedPhaseFold.phaseBank, hw0, hw1]
  by_cases h274 : i.val = 274
  · simp [h274]
  · by_cases h275 : i.val = 275
    · simp [h275]
    · simp [h274, h275, C10TailUniformSlots.phaseIndex]

/-- The penalty fold slots 215 and 218, as numbers. -/
theorem fd_penalty_215 : (Fd sources p k r scratch .penalty 215).val =
    PCJda54a286946142d3_BranchPhases.offset sources p k r + 342 := by
  simp [Fd, CloseoutFinalC10RetainedPhaseFold.foldSlots, CloseoutFinalC10RetainedPhaseFold.tailSlots,
    C10TailVerdict.scratchT]

theorem fd_penalty_218 : (Fd sources p k r scratch .penalty 218).val =
    PCJda54a286946142d3_BranchPhases.offset sources p k r + 132 := by
  simp [Fd, CloseoutFinalC10RetainedPhaseFold.foldSlots, CloseoutFinalC10RetainedPhaseFold.tailSlots,
    C10TailUniformSlots.phaseIndex]

/-- Every penalty fold slot sits below 278 or at `offset+124` and above. -/
theorem fd_penalty_range (i : Fin 219) :
    (Fd sources p k r scratch .penalty i).val < 278 ∨
      PCJda54a286946142d3_BranchPhases.offset sources p k r + 124 ≤ (Fd sources p k r scratch .penalty i).val := by
  have hi := i.isLt
  simp only [Fd, CloseoutFinalC10RetainedPhaseFold.foldSlots, CloseoutFinalC10RetainedPhaseFold.tailSlots,
    CloseoutFinalC10RetainedPhaseFold.phaseBank, C10TailVerdict.scratchT, C10TailUniformSlots.phaseIndex]
  split_ifs <;> simp_all
  omega

/-- The penalty loop start misses the first-entry slots except at word slot 218. -/
theorem penaltyA0_off (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch))
    (h : t.val ≠ 218 ∧ (t.val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 124 ∨
      (t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 124 ∧
       t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 125 ∧
       t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 135 ∧
       t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 136 ∧
       t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 137 ∧
       t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 689 ∧
       t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 817 ∧
       t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 967 ∧
       t.val ≠ PCJda54a286946142d3_BranchPhases.offset sources p k r + 1095))) :
    penaltyA0 sources p den hden k r scratch n x bits hp t =
      PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp
        (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) := by
  apply install_other
  intro i he
  have hv := congrArg Fin.val he
  fin_cases i <;> simp [fSlots, CloseoutFinalC10FirstPhaseEntry.firstSlots] at hv <;> omega

/-- **The penalty loop start**, in exactly the forms `fields_E1`/`field_E2`/`fields_E3`/`fields_E4`/
`fields_E5` consume (rows C1/C2 → E1–E5 at `j = 0`), plus the entry's `hdriver`/`hword` (row C4).
`A 0 := penaltyA0`, `H 0 := S.heads ∘ body`, mode `S.mode`. -/
theorem penalty_start :
    let clock := PolynomialClock.ordinaryClock k
    let oracle := C10TotalDecode.oracleOf sources k clock p.degree n bits
    let mode := PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp
    let A0 := penaltyA0 sources p den hden k r scratch n x bits hp
    let H0 := fun j => PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch
      (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j)
    (∀ i : Fin 278, 2 ≤ i.val → i.val < 215 → i.val ≠ 81 → i.val ≠ 90 → A0 (Wd sources p k r scratch .penalty i) = []) ∧
    (∀ i : Fin 278, 219 ≤ i.val → A0 (Wd sources p k r scratch .penalty i) = []) ∧
    A0 (Fd sources p k r scratch .penalty 215) = [] ∧
    A0 (Fd sources p k r scratch .penalty 218) = [] ∧
    A0 (Wd sources p k r scratch .penalty 218) = List.replicate (C10PartsSchedule.entryWidthSchedule sources k r n) true ∧
    A0 (Wd sources p k r scratch .penalty 81) = [] ∧
    A0 (Wd sources p k r scratch .penalty 90) = CompareMachine.word 0 ∧
    (∀ i, H0 (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) = 0) ∧
    H0 (PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch) = 0 ∧
    A0 (PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch) = List.replicate (NC sources k clock x oracle) true ∧
    (∀ i, A0 (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) = CD sources k clock x oracle 0 i) ∧
    (∀ i, H0 (Wd sources p k r scratch .penalty i) = 0) ∧
    (∀ i, H0 (Fd sources p k r scratch .penalty i) = 0) ∧
    PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch (PCJda54a286946142d3_BranchPhases.driver sources p k r scratch) = 1 ∧
    penaltyMiddle sources p den hden k r scratch n x bits hp (PCJda54a286946142d3_BranchPhases.driver sources p k r scratch) =
      UnaryTemplate.tape (NC sources k clock x oracle) := by
  dsimp only
  obtain ⟨_hmode, hlow, h90, _h218, hterm, hfar, hcache, hdrv, hheads, hdh⟩ :=
    penalty_bank sources p den hden k r scratch n x bits hp
  have hP := size_302 sources p k r
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have hoff : PCJda54a286946142d3_BranchPhases.offset sources p k r =
      WorkspaceSelectedEntry.size sources k r p.clauseDegree + WorkspaceSelectedAdmission.originalTapes sources p k - 2 := rfl
  have ht := WorkspaceSelectedEntryReady.old_size sources p k
  have spec := firstLocal_spec (C10PartsSchedule.entryWidthSchedule sources k r n)
  have hcv : ∀ i, (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch
      (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i).val < 2 ∨
      (WorkspaceSelectedEntry.size sources k r p.clauseDegree ≤ (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch
        (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i).val ∧
       (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch
        (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i).val < PCJda54a286946142d3_BranchPhases.offset sources p k r) := by
    intro i
    generalize PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp = mode
    have hc := (WorkspaceSelectedEntryReady.cache sources p k mode i).isLt
    change (if (WorkspaceSelectedEntryReady.cache sources p k mode i).val<2 then
        (WorkspaceSelectedEntryReady.cache sources p k mode i).val else
        WorkspaceSelectedEntry.size sources k r p.clauseDegree+
          (WorkspaceSelectedEntryReady.cache sources p k mode i).val-2) < 2 ∨ _
    change _ ∨ (_ ≤ (if (WorkspaceSelectedEntryReady.cache sources p k mode i).val<2 then
        (WorkspaceSelectedEntryReady.cache sources p k mode i).val else
        WorkspaceSelectedEntry.size sources k r p.clauseDegree+
          (WorkspaceSelectedEntryReady.cache sources p k mode i).val-2) ∧
      (if (WorkspaceSelectedEntryReady.cache sources p k mode i).val<2 then
        (WorkspaceSelectedEntryReady.cache sources p k mode i).val else
        WorkspaceSelectedEntry.size sources k r p.clauseDegree+
          (WorkspaceSelectedEntryReady.cache sources p k mode i).val-2) < _)
    rw [hoff]
    split_ifs <;> omega
  have tv : (PCJ30aa6f1b7c2a4221_.Selected.terminal sources p k r scratch).val =
      PCJda54a286946142d3_BranchPhases.offset sources p k r + 53 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hdh, ?_⟩
  · intro i h2 h215 h81 h90'
    have hv := wd_penalty_val sources p k r scratch i
    rw [if_neg (by omega), if_neg (by omega)] at hv
    rw [penaltyA0_off sources p den hden k r scratch n x bits hp _ (by omega)]
    exact hlow _ (by omega) (by omega) (by omega) (by omega) (by omega)
  · intro i h219
    have hv := wd_penalty_val sources p k r scratch i
    have hi := i.isLt
    by_cases h274 : i.val = 274 ∨ i.val = 275
    · rw [penaltyA0_off sources p den hden k r scratch n x bits hp _ (by split_ifs at hv <;> omega)]
      exact hfar _ (by split_ifs at hv <;> omega)
    · rw [if_neg (by omega), if_neg (by omega)] at hv
      rw [penaltyA0_off sources p den hden k r scratch n x bits hp _ (by omega)]
      exact hlow _ (by omega) (by omega) (by omega) (by omega) (by omega)
  · have hv := fd_penalty_215 sources p k r scratch
    rw [penaltyA0_off sources p den hden k r scratch n x bits hp _ (by omega)]
    exact hfar _ (by omega)
  · have hv := fd_penalty_218 sources p k r scratch
    rw [penaltyA0_off sources p den hden k r scratch n x bits hp _ (by omega)]
    exact hfar _ (by omega)
  · have he : Wd sources p k r scratch .penalty 218 = fSlots sources p k r scratch 0 := by
      apply Fin.ext
      rw [wd_penalty_val]
      simp [fSlots, CloseoutFinalC10FirstPhaseEntry.firstSlots]
    change install _ _ _ _ = _
    rw [he, install_slot _ (CloseoutFinalC10FirstPhaseEntry.slots_injective _ _ _ _)]
    exact spec.2.1
  · have hv := wd_penalty_val sources p k r scratch 81
    rw [penaltyA0_off sources p den hden k r scratch n x bits hp _ (by simp at hv; omega)]
    exact hlow _ (by simp at hv; omega) (by simp at hv; omega) (by simp at hv; omega)
      (by simp at hv; omega) (by simp at hv; omega)
  · have hv := wd_penalty_val sources p k r scratch 90
    rw [penaltyA0_off sources p den hden k r scratch n x bits hp _ (by simp at hv; omega)]
    have he : Wd sources p k r scratch .penalty 90 = lowIdx sources p k r scratch 90 (by omega) := by
      apply Fin.ext
      rw [hv]
      rfl
    rw [he]
    exact h90
  · intro i
    apply hheads
    rcases hcv i with h | h <;> omega
  · apply hheads
    rw [tv]; omega
  · rw [penaltyA0_off sources p den hden k r scratch n x bits hp _ (by rw [tv]; omega)]
    exact hterm
  · intro i
    rw [penaltyA0_off sources p den hden k r scratch n x bits hp _ (by rcases hcv i with h | h <;> omega)]
    exact hcache i
  · intro i
    apply hheads
    have hv := wd_penalty_val sources p k r scratch i
    have hi := i.isLt
    split_ifs at hv <;> omega
  · intro i
    apply hheads
    rcases fd_penalty_range sources p k r scratch i with h | h <;> omega
  · change install _ _ _ _ = _
    rw [install_other _ _ _ _ (fun i he => PCJda54a286946142d3_BranchPhases.body_ne_driver sources p k r scratch i he)]
    exact hdrv

end entry

/-! ## 4. Row C3: the moment/clause entry (focused cache erase) and their loop start -/

section later
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k r scratch : Nat)
  (clock : OrdinaryClock (fun n => n^(k+2))) {n : Nat} (x : BitInput n)
  (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))

/-- The query-cache capacity `C` of the actual request. -/
abbrev capC := PCPPQueryCachedBounds.capacity (CloseoutLanguage.selectedPCPP sources)
  ((req sources k clock x oracle).circuit.size+(req sources k clock x oracle).arity)

theorem capC_room : NC sources k clock x oracle + 2 ≤ capC sources k clock x oracle := by
  have hc := (PCPPQueryBounds.components (CloseoutLanguage.selectedPCPP sources) (req sources k clock x oracle)).2.2.2.2.2.2.1
  have hm := PCPPQueryCachedBounds.majorant_bound (CloseoutLanguage.selectedPCPP sources)
    ((req sources k clock x oracle).circuit.size+(req sources k clock x oracle).arity)
  have h1 := (PCPPQueryBounds.components (CloseoutLanguage.selectedPCPP sources) (req sources k clock x oracle)).1
  unfold PCPPQueryBounds.majorant at hm
  change 2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits + 2 ≤ _
  nlinarith

/-- The erase's exit on the cache's (pair, driver, log) = (14, 17, 18). -/
def laterE (C : Nat) : Fin 3 → List Bool :=
  ![List.replicate C false, List.replicate C true, List.replicate (C+1) false]

theorem laterE_0 (C : Nat) : laterE C 0 = List.replicate C false := rfl
theorem laterE_1 (C : Nat) : laterE C 1 = List.replicate C true := rfl
theorem laterE_2 (C : Nat) : laterE C 2 = List.replicate (C+1) false := rfl

theorem pad_tape0 (C : Nat) (h : 2 ≤ C) : ZeroPadding.pad C (UnaryTemplate.tape 0) = List.replicate C false := by
  have ht0 : UnaryTemplate.tape 0 = List.replicate 2 false := by simp [UnaryTemplate.tape]
  rw [ht0]
  exact ExtDecompositionBatch.pad_replicate_false _ 2 h

/-- A three-tape `Fin.addCases` bank is the vector of its three words (kernel-cheap form). -/
theorem addCases3 (a b c : List Bool) :
    (Fin.addCases (Fin.addCases (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)) (fun _ : Fin 1 => c) :
      Fin (1+1+1) → List Bool) = ![a, b, c] := by
  funext j
  fin_cases j <;> simp [Fin.addCases]

/-- **The moment/clause loop-start bank** `A 0`, from the previous phase's exit `tin`. -/
def laterA0 (mode : Bool) (tin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool) :
    Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool :=
  install (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode)
    (fun j => tin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j))
    (install (![14,17,18] : Fin 3 → Fin 19)
      (fun j => tin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch
        (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode j)))
      (laterE (capC sources k clock x oracle)))

/-- **The moment/clause middle bank.** -/
def laterMiddle (mode : Bool) (tin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool) :
    Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool :=
  install (PCJda54a286946142d3_BranchPhases.body sources p k r scratch) tin
    (laterA0 sources p k r scratch clock x oracle mode tin)

theorem slots3_injective : Function.Injective (![14,17,18] : Fin 3 → Fin 19) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

/-- The clause index is written only on cache tape 14. -/
theorem data_index (src : List Bool) (ar N C : Nat) (pair : List Bool) (i : Fin 19) (hi : i ≠ 14) :
    PCPPQueryClauseReuse.data src ar N C pair i = PCPPQueryClauseReuse.data src ar 0 C pair i := by
  fin_cases i <;> simp_all [PCPPQueryClauseReuse.data]

theorem cd_14 (src : List Bool) (ar N C : Nat) (res : List Bool) :
    PCPPQueryIndexPadding.clauseData src ar N C res 14 = ZeroPadding.pad C (UnaryTemplate.tape N) := by
  simp [PCPPQueryIndexPadding.clauseData]

theorem cd_17 (src : List Bool) (ar N C : Nat) (res : List Bool) :
    PCPPQueryIndexPadding.clauseData src ar N C res 17 = List.replicate C true := by
  simp [PCPPQueryIndexPadding.clauseData, PCPPQueryClauseReuse.data]

theorem cd_18 (src : List Bool) (ar N C : Nat) (res : List Bool) :
    PCPPQueryIndexPadding.clauseData src ar N C res 18 = List.replicate (C+1) false := by
  simp [PCPPQueryIndexPadding.clauseData, PCPPQueryClauseReuse.data]

theorem cd_index (src : List Bool) (ar N C : Nat) (res : List Bool) (i : Fin 19) (hi : i ≠ 14) :
    PCPPQueryIndexPadding.clauseData src ar N C res i = PCPPQueryIndexPadding.clauseData src ar 0 C res i := by
  simp only [PCPPQueryIndexPadding.clauseData, if_neg hi]
  exact data_index src ar N C res i hi

/-- A three-point function agrees with its vector (generic, so the case split stays small). -/
theorem vec3 {α : Type} (f : Fin 3 → α) (a b c : α) (h0 : f 0 = a) (h1 : f 1 = b) (h2 : f 2 = c) :
    ∀ j, f j = ![a, b, c] j := by
  intro j
  fin_cases j
  · exact h0
  · exact h1
  · exact h2

/-- The erase's footprint inside the cache (generic in the ambient bank). -/
theorem erase_cache {B : Nat} (cache : Fin 19 → Fin B) (hc : Function.Injective cache)
    (A : Fin B → List Bool) (E : Fin 3 → List Bool) (i : Fin 19) :
    install cache A (install (![14,17,18] : Fin 3 → Fin 19) (fun j => A (cache j)) E) (cache i) =
      if i = 14 then E 0 else if i = 17 then E 1 else if i = 18 then E 2 else A (cache i) := by
  rw [install_slot _ hc]
  by_cases h14 : i = 14
  · subst h14
    exact install_slot (![14,17,18] : Fin 3 → Fin 19) slots3_injective _ E 0
  by_cases h17 : i = 17
  · subst h17
    exact install_slot (![14,17,18] : Fin 3 → Fin 19) slots3_injective _ E 1
  by_cases h18 : i = 18
  · subst h18
    exact install_slot (![14,17,18] : Fin 3 → Fin 19) slots3_injective _ E 2
  rw [if_neg h14, if_neg h17, if_neg h18]
  apply install_other
  intro j he
  fin_cases j
  · exact h14 he.symm
  · exact h17 he.symm
  · exact h18 he.symm

/-- **C3 (`hentry`, moment/clause).** From any entry bank whose query cache is at the end-of-loop
state `clauseData N` with zero cache heads, the fixed moment/clause phase entry (a focused erase of
cache 14 driven by cache 17, logged on 18) runs at `2*C+4`, heads unchanged, to `laterMiddle`. -/
theorem later_entry (mode : Bool) (ph : Phase) (hph : ph = .moment ∨ ph = .clause)
    (hin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → Nat)
    (tin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool)
    (hcache : ∀ i, tin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch
      (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i)) =
      CD sources k clock x oracle (NC sources k clock x oracle) i)
    (hheads : ∀ i, hin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch
      (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i)) = 0) :
    Step (RecoveryFocus.machine (PCJda54a286946142d3_BranchPhases.body sources p k r scratch)
        (PCJda54a286946142d3_BranchPhases.phaseEntry sources p k r scratch mode ph).2)
      (2*capC sources k clock x oracle+4) hin tin hin (laterMiddle sources p k r scratch clock x oracle mode tin) := by
  have room := capC_room sources k clock x oracle
  have hb : ∀ i : Fin 1, ((fun _ : Fin 1 => ZeroPadding.pad (capC sources k clock x oracle)
      (UnaryTemplate.tape (NC sources k clock x oracle))) i).length ≤ capC sources k clock x oracle := by
    intro i
    have hl : (UnaryTemplate.tape (NC sources k clock x oracle)).length = NC sources k clock x oracle + 2 := by
      simp [UnaryTemplate.tape]
    change (ZeroPadding.pad _ _).length ≤ _
    rw [ZeroPadding.pad_length, hl]
    omega
  have er := Step.of_ready (RecoveryScratchErase.erase_ready (capC sources k clock x oracle)
    (capC sources k clock x oracle+1) _ hb)
  rw [addCases3, addCases3, max_self] at er
  have hH : ∀ j : Fin 3, (fun i => hin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch
      (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i))) ((![14,17,18] : Fin 3 → Fin 19) j) =
      (fun _ => 0) j :=
    fun j => hheads _
  have hA : ∀ j : Fin 3, (fun i => tin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch
      (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i))) ((![14,17,18] : Fin 3 → Fin 19) j) =
      (![ZeroPadding.pad (capC sources k clock x oracle) (UnaryTemplate.tape (NC sources k clock x oracle)),
        List.replicate (capC sources k clock x oracle) true,
        List.replicate (capC sources k clock x oracle+1) false] : Fin 3 → List Bool) j := by
    refine vec3 _ _ _ _ ?_ ?_ ?_
    · show tin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch
        (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode 14)) = _
      rw [hcache]
      exact cd_14 _ _ _ _ _
    · show tin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch
        (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode 17)) = _
      rw [hcache]
      exact cd_17 _ _ _ _ _
    · show tin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch
        (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode 18)) = _
      rw [hcache]
      exact cd_18 _ _ _ _ _
  have s1 := (er.dock (![14,17,18] : Fin 3 → Fin 19) slots3_injective
      (fun i => hin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch
        (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i)))
      (fun i => tin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch
        (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i))) hH hA).congr
    (dockH_existing (![14,17,18] : Fin 3 → Fin 19)
      (fun i => hin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch
        (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i))) (fun _ => 0) hH) rfl
  have s2 := (s1.dock (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode)
    (PCJ30aa6f1b7c2a4221_.Selected.cache_injective sources p k r scratch mode)
    (fun j => hin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j))
    (fun j => tin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j)) (fun _ => rfl) (fun _ => rfl)).congr
    (dockH_existing _ _ _ (fun _ => rfl)) rfl
  have s3 := (s2.dock (PCJda54a286946142d3_BranchPhases.body sources p k r scratch)
    (PCJda54a286946142d3_BranchPhases.body_injective sources p k r scratch) hin tin (fun _ => rfl) (fun _ => rfl)).congr
    (dockH_existing _ _ _ (fun _ => rfl)) rfl
  rcases hph with rfl | rfl <;> exact s3

/-- The moment/clause loop start: the cache is back at `clauseData 0`. -/
theorem laterA0_cache (mode : Bool) (tin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool)
    (hcache : ∀ i, tin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch
      (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i)) =
      CD sources k clock x oracle (NC sources k clock x oracle) i) (i : Fin 19) :
    laterA0 sources p k r scratch clock x oracle mode tin
      (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) = CD sources k clock x oracle 0 i := by
  have room := capC_room sources k clock x oracle
  unfold laterA0
  rw [erase_cache _ (PCJ30aa6f1b7c2a4221_.Selected.cache_injective sources p k r scratch mode)]
  by_cases h14 : i = 14
  · subst h14
    rw [if_pos rfl, laterE_0, CD, cd_14, pad_tape0 _ (le_trans (Nat.le_add_left 2 _) room)]
  rw [if_neg h14]
  by_cases h17 : i = 17
  · subst h17
    rw [if_pos rfl, laterE_1, CD, cd_17]
  rw [if_neg h17]
  by_cases h18 : i = 18
  · subst h18
    rw [if_pos rfl, laterE_2, CD, cd_18]
  rw [if_neg h18, hcache]
  exact cd_index _ _ _ _ _ i h14

theorem laterA0_off (mode : Bool) (tin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool)
    (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch))
    (ht : ∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i) :
    laterA0 sources p k r scratch clock x oracle mode tin t = tin (PCJda54a286946142d3_BranchPhases.body sources p k r scratch t) :=
  install_other _ _ _ _ (fun i he => ht i he.symm)

end later

end
end NearCubicWires.SourcePhase
end

import Proof.Packets.SrcRes284Exp
import Proof.MachineModel.TopDownWorkspaceSelectedEntry

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceStart.Res284
open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.CloseoutFinal.C10PrologueUniform
noncomputable section

theorem prologue_run_of_seed6 (e : ℕ) (entryWidth q : ℕ → ℕ) (clauseDegree : ℕ) (seedFuel : ℕ → ℕ)
    {ss : ℕ} (seed : Machine (218 + (60 + (e + 23)) + 1) ss)
    (len : ℕ) (x : BitInput len) (bits : List Bool) (junk : ℕ → List Bool)
    (hwindow : ∀ v, 279 ≤ v → v ≤ 300 → junk v = [])
    (hcounter : junk (301 + e) = [])
    (hseedStep : Step seed (seedFuel len) (fun _ => 0)
      (bank [] [] [] (List.ofFn x) bits (fun _ => [])) (fun _ => 0)
      (bank [] [] (List.replicate (entryWidth len) true) (List.ofFn x) bits
        (seedTapes (clauseWidth clauseDegree (q len)) junk))) :
    ∃ w : ℕ → List Bool,
      Step (prologueMachine e seed) (prologueFuel clauseDegree q seedFuel len) (fun _ => 0)
        (bank [] [] [] (List.ofFn x) bits (fun _ => []))
        (Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun _ : Fin 1 => 1))
        (Fin.addCases (motive := fun _ => List Bool)
          (bank [] (CompareMachine.word 0) (List.replicate (entryWidth len) true)
            (List.ofFn x) bits w)
          (fun _ : Fin 1 => CompareMachine.word (2 ^ clauseWidth clauseDegree (q len)))) ∧
      (∀ v, 301 ≤ v → v < 301 + e → w v = junk v) ∧
      w 284 = Res284.expWork (clauseWidth clauseDegree (q len)) := by
  obtain ⟨w2, hzero, hw2⟩ :=
    zeroCount_run e (List.replicate (entryWidth len) true) (List.ofFn x) bits
      (seedTapes (clauseWidth clauseDegree (q len)) junk)
      (by rw [seedTapes, if_neg (by omega)]; exact hwindow 300 (by omega) (by omega))
  obtain ⟨H3, A3, henv, hzero3, _, hcount, h6, hrest3⟩ :=
    Res284.envelopeCounter_dock6 (m := 218 + (60 + (e + 23)) + 1)
      clauseDegree (q len) (envSlots e) (envSlots_injective e) (fun _ => 0)
      (bank [] (CompareMachine.word 0) (List.replicate (entryWidth len) true)
        (List.ofFn x) bits w2) (fun _ => rfl)
      (by rw [bank_apply, envSlots_zero, bankAt_scratch _ _ _ _ _ _ _ (by omega),
          hw2 278 (by omega), seedTapes, if_pos rfl])
      (by
        intro j hj
        obtain ⟨hlow, hne⟩ := envSlots_bounds e j hj
        rw [bank_apply, bankAt_scratch _ _ _ _ _ _ _ (by omega), hw2 _ hne, seedTapes,
          if_neg (by omega)]
        rcases envSlots_window e j hj with h | h
        · exact hwindow _ (by omega) (by omega)
        · rw [h]; exact hcounter)
  have hH3 : H3 = fun _ => 0 := funext hzero3
  refine ⟨fun v => if h : v < 218 + (60 + (e + 23)) + 1 then A3 ⟨v, h⟩ else [], ?_, ?_, ?_⟩
  · have hbumped := bumpCounter_run e A3
    rw [← hH3] at hbumped
    have hchain := hseedStep.seq (hzero.seq (henv.seq hbumped))
    have hA3 : A3 = Fin.addCases (motive := fun _ => List Bool)
        (bank [] (CompareMachine.word 0) (List.replicate (entryWidth len) true)
          (List.ofFn x) bits
          (fun v => if h : v < 218 + (60 + (e + 23)) + 1 then A3 ⟨v, h⟩ else []))
        (fun _ : Fin 1 => CompareMachine.word (2 ^ clauseWidth clauseDegree (q len))) := by
      funext i
      by_cases hi : i.val = 301 + e
      · have hc : i = counterTape e := Fin.ext hi
        rw [hc, counterTape_natAdd e, Fin.addCases_right, ← counterTape_natAdd e,
          ← envSlots_eighteen e]
        exact hcount
      · have hlt : i.val < 218 + (60 + (e + 23)) := by have := i.isLt; omega
        have hl : i = Fin.castAdd 1 (⟨i.val, hlt⟩ : Fin (218 + (60 + (e + 23)))) := Fin.ext rfl
        have hrhs : Fin.addCases (motive := fun _ => List Bool)
            (bank [] (CompareMachine.word 0) (List.replicate (entryWidth len) true)
              (List.ofFn x) bits
              (fun v => if h : v < 218 + (60 + (e + 23)) + 1 then A3 ⟨v, h⟩ else []))
            (fun _ : Fin 1 => CompareMachine.word (2 ^ clauseWidth clauseDegree (q len))) i
            = bankAt [] (CompareMachine.word 0) (List.replicate (entryWidth len) true)
              (List.ofFn x) bits
              (fun v => if h : v < 218 + (60 + (e + 23)) + 1 then A3 ⟨v, h⟩ else []) i.val := by
          conv_lhs => rw [hl]
          rw [Fin.addCases_left]
          rfl
        rw [hrhs]
        by_cases h278 : 278 ≤ i.val
        · rw [bankAt_scratch _ _ _ _ _ _ _ h278]
          show A3 i = (if h : i.val < 218 + (60 + (e + 23)) + 1 then A3 ⟨i.val, h⟩ else [])
          rw [dif_pos i.isLt]
        · have hne : ∀ j, envSlots e j ≠ i := by
            intro j hj
            by_cases hj0 : j = 0
            · rw [hj0] at hj
              exact h278 (by rw [← hj, envSlots_zero])
            · obtain ⟨hlow, _⟩ := envSlots_bounds e j hj0
              exact h278 (by rw [← hj]; omega)
          rw [hrest3 i hne, bank_apply]
          unfold bankAt
          split_ifs <;> rfl
    rw [hA3] at hchain
    exact hchain
  · intro v hvlo hvhi
    change (if h : v < 218 + (60 + (e + 23)) + 1 then A3 ⟨v, h⟩ else []) = junk v
    rw [dif_pos (by omega)]
    have hne : ∀ j, envSlots e j ≠ (⟨v, by omega⟩ : Fin (218 + (60 + (e + 23)) + 1)) := by
      intro j hj
      have hv : (envSlots e j).val = v := congrArg Fin.val hj
      by_cases h0 : j = 0
      · rw [h0, envSlots_zero] at hv
        omega
      · rcases envSlots_window e j h0 with h | h <;> omega
    rw [hrest3 _ hne]
    change bankAt [] (CompareMachine.word 0) (List.replicate (entryWidth len) true)
      (List.ofFn x) bits w2 v = junk v
    rw [bankAt_scratch _ _ _ _ _ _ _ (by omega),
      hw2 v (by omega), seedTapes, if_neg (by omega)]
  · show (if h : 284 < 218 + (60 + (e + 23)) + 1 then A3 ⟨284, h⟩ else []) = _
    rw [dif_pos (by omega)]
    have e6 : (⟨284, by omega⟩ : Fin (218 + (60 + (e + 23)) + 1)) = envSlots e 6 := Fin.ext rfl
    rw [e6]
    exact h6

/-- `Prologue` with the exponentiator's work word on scratch 284. -/
def Prologue6 (extra : ℕ) (entryWidth q : ℕ → ℕ) (clauseDegree : ℕ) (preFuel : ℕ → ℕ)
    {ps : ℕ} (pre : Machine (218 + (60 + extra) + 1) ps) : Prop :=
  ∀ (len : ℕ) (x : BitInput len) (bits : List Bool),
    ∃ w : ℕ → List Bool,
      Step pre (preFuel len) (fun _ => 0)
        (bank [] [] [] (List.ofFn x) bits (fun _ => []))
        (Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun _ : Fin 1 => 1))
        (Fin.addCases (motive := fun _ => List Bool)
          (bank [] (CompareMachine.word 0) (List.replicate (entryWidth len) true)
            (List.ofFn x) bits w)
          (fun _ : Fin 1 => CompareMachine.word (2 ^ clauseWidth clauseDegree (q len)))) ∧
      w 284 = Res284.expWork (clauseWidth clauseDegree (q len))

theorem prologue_of_seed6 (e : ℕ) (entryWidth q : ℕ → ℕ) (clauseDegree : ℕ) (seedFuel : ℕ → ℕ)
    {ss : ℕ} (seed : Machine (218 + (60 + (e + 23)) + 1) ss)
    (hseed : Seed e entryWidth q clauseDegree seedFuel seed) :
    Prologue6 (e + 23) entryWidth q clauseDegree (prologueFuel clauseDegree q seedFuel)
      (prologueMachine e seed) := by
  intro len x bits
  obtain ⟨junk, hb, hc, hs⟩ := hseed len x bits
  obtain ⟨w, hrun, _, h284⟩ := prologue_run_of_seed6 e entryWidth q clauseDegree seedFuel seed
    len x bits junk hb hc hs
  exact ⟨w, hrun, h284⟩

section sched
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SeedEngine

theorem prologue_at_schedule6 (sources : RepairSource.EightSources) (k r D : ℕ) (hD : 1 ≤ D)
    {tw sw : ℕ} (W : Machine tw sw) (inW qW : Fin tw) (hne : inW ≠ qW) (wfuel : ℕ → ℕ)
    (hwidth : ∀ (len : ℕ) (x : BitInput len), ∃ wout : Fin tw → List Bool,
      wout inW = frame (List.ofFn x) ∧
      wout qW = List.replicate
        (RepairSource.CloseoutFinal.C10PartsSchedule.widthAt sources k len) true ∧
      Step W (wfuel len) (fun _ => 0)
        (fun j => if j = inW then frame (List.ofFn x) else []) (fun _ => 0) wout) :
    Prologue6 (tapesOf tw r D + 23)
      (RepairSource.CloseoutFinal.C10PartsSchedule.entryWidthSchedule sources k r)
      (RepairSource.CloseoutFinal.C10PartsSchedule.widthAt sources k) D
      (prologueFuel D
        (RepairSource.CloseoutFinal.C10PartsSchedule.widthAt sources k)
        (engineFuel r D wfuel
          (RepairSource.CloseoutFinal.C10PartsSchedule.thresholdFloor sources)
          (RepairSource.CloseoutFinal.C10PartsSchedule.widthAt sources k)))
      (prologueMachine (tapesOf tw r D)
        (RecoveryFocus.machine (bankSlots tw r D inW)
          (engineMachine r D W qW
            (RepairSource.CloseoutFinal.C10PartsSchedule.thresholdFloor sources)))) :=
  prologue_of_seed6 (tapesOf tw r D)
    (RepairSource.CloseoutFinal.C10PartsSchedule.entryWidthSchedule sources k r)
    (RepairSource.CloseoutFinal.C10PartsSchedule.widthAt sources k) D
    (engineFuel r D wfuel
      (RepairSource.CloseoutFinal.C10PartsSchedule.thresholdFloor sources)
      (RepairSource.CloseoutFinal.C10PartsSchedule.widthAt sources k))
    _
    (seed_of_widthReader r D hD W inW qW hne
      (RepairSource.CloseoutFinal.C10PartsSchedule.thresholdFloor sources)
      (RepairSource.CloseoutFinal.C10PartsSchedule.widthAt sources k) wfuel hwidth)

end sched

section entry
open NearCubicWires.P1TopDown NearCubicWires.P1TopDown.WorkspaceSelectedEntry
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairOrdinary.CloseoutWitness NearCubicWires.RepairRepresentation
open NearCubicWires.P1TopDown.WorkspaceSelectedAdmission (originalTapes)
open NearCubicWires.P1TopDown.WorkspaceSelectedProgram (finalBank)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_other)

theorem local_run6 (sources : EightSources) (k r D : Nat) (hD : 1 ≤ D)
    (n : Nat) (x : BitInput n) (bits : List Bool) :
    ∃ w, Step (program sources k r D).2 (C10EngineFuelSeam.enginePreFuel sources k r D n)
      (fun _ => 0) (C10SupplierCall.bank [] [] [] (List.ofFn x) bits (fun _ => []))
      (outputHeads sources k r D) (output sources k r D n (List.ofFn x) bits w) ∧
      w 284 = Res284.expWork (clauseWidth D (C10PartsSchedule.widthAt sources k n)) := by
  unfold program
  exact prologue_at_schedule6 sources k r D hD
    (CloseoutFinalC10SeedEngine.widthReader sources k) (CloseoutFinalC10SeedEngine.readerIn sources k)
    (CloseoutFinalC10SeedEngine.readerQ sources k) (CloseoutFinalC10SeedEngine.readerIn_ne sources k)
    (CloseoutFinalC10SeedEngine.readerFuel sources k) (CloseoutFinalC10SeedEngine.width_reader sources k) n x bits

theorem entry_run6 (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k r extra : Nat)
    (hspace : size sources k r p.clauseDegree ≤ extra)
    (n : Nat) (x : BitInput n) (bits : List Bool)
    (A : Fin (originalTapes sources p k) → List Bool) (L : Nat)
    (originals : WorkspaceSelectedOriginals.Originals sources p k x bits A) :
    let ht : 2 ≤ originalTapes sources p k := by
      dsimp [originalTapes,WorkspaceBoundedGateEntry.originalTapes,WorkspaceBoundedAdmission.tapes,HeaderDock.tapes]
      omega
    let port := slots ht hspace
    ∃ w, Step (RecoveryFocus.machine port (program sources k r p.clauseDegree).2)
      (C10EngineFuelSeam.enginePreFuel sources k r p.clauseDegree n) (fun _ => 0) (finalBank A L extra)
      (dockH port (fun _ => 0) (outputHeads sources k r p.clauseDegree))
      (install port (finalBank A L extra) (output sources k r p.clauseDegree n (List.ofFn x) bits w)) ∧
      (∀ v, (∀ i, port i ≠ v) →
        install port (finalBank A L extra) (output sources k r p.clauseDegree n (List.ofFn x) bits w) v =
          finalBank A L extra v) ∧
      w 284 = Res284.expWork (clauseWidth p.clauseDegree (C10PartsSchedule.widthAt sources k n)) := by
  intro ht port
  obtain ⟨w, hr, h284⟩ := local_run6 sources k r p.clauseDegree p.hD n x bits
  have inp := input_at_slots ht hspace A L (List.ofFn x) bits originals.1 originals.2.1
  exact ⟨w, hr.dock port (slots_injective ht hspace) (fun _ => 0) (finalBank A L extra)
    (fun _ => rfl) inp, fun v hv => install_other port _ _ v hv, h284⟩

end entry

end
end NearCubicWires.SourceStart.Res284


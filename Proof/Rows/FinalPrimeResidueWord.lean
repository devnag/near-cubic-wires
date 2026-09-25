import Proof.Rows.FinalPrimeRow

/-! # GAP 2: materialising the residue as one framed word on one tape

`RepairCloseoutFinalPrimeRow.residue_loop` leaves the residue of the target
split across two candidate words `T`, `U` and a one-cell flag `F`, selected by
`residueWord`.  Everything downstream (modular multiply-accumulate, the
zero-test of a trial division) wants a single framed word.

This file supplies the missing selection pass and joins it to the loop.

The extra pass is a flat three-tape worker `machine : Machine 3 6` docked into
the *existing* seven-tape bank by `RecoveryFocus`, and joined by
`Composition`, which adds finite control states but no tapes.  So the tape
nesting depth is unchanged: `pass → MaskedReset → RepeatMachine` is still the
whole `Fin.addCases` stack, and every port equality the elaborator would
otherwise have to unfold through that stack is hoisted into the named lemmas
`ambientHeads_port` / `ambientTapes_port` below.

No head reset is needed: the loop body already resets the word heads, so the
selection pass starts with its own ports at zero, and it is the last stage.
-/
namespace NearCubicWires.RepairOrdinary.FinalPrimeResidue
open LocalBitMultitape RecoveryExecution RadixSemantics ExtDecompositionBatch
open RepairSource.VerifierDecoding RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## 1. The selection pass -/

def mstate (sel : Bool) : Fin 6 := if sel then 3 else 2
def bstate (sel : Bool) : Fin 6 := if sel then 5 else 4
def selOf (q : Fin 6) : Bool := decide (q.val % 2 = 1)


def mv : Fin 3 → HeadMove := fun i => if i.val ≤ 1 then .right else .stay

/-- Tapes: `0 = D` (destination, overwritten in place), `1 = S` (the other
candidate), `2 = F` (the one-cell flag; its head never moves). -/
def machine : Machine 3 6 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q scanned =>
    if q.val = 0 then some ⟨mstate (scanned 2), fun _ => none, fun _ => .stay⟩
    else if q.val = 1 then none
    else if q.val < 4 then
      (if scanned 0 then some ⟨bstate (selOf q), fun _ => none, mv⟩
        else some ⟨1, fun _ => none, mv⟩)
    else
      some ⟨mstate (selOf q),
        fun i => if i.val = 0 then some (if selOf q then scanned 1 else scanned 0) else none, mv⟩

def cfg (q : Fin 6) (D S F : List Bool) (pos : ℕ) : Configuration 3 6 :=
  ⟨q, ![pos, pos, 0], ![D, S, F]⟩

theorem write_mid (pre tail : List Bool) (old v : Bool) :
    writeTapeBit (pre ++ old :: tail) pre.length v = pre ++ v :: tail := by
  induction pre with
  | nil => rfl
  | cons b pre ih => simpa [writeTapeBit] using congrArg (List.cons b) ih

theorem entry_step (D S F : List Bool) (sel : Bool) (hF : readTapeBit F 0 = sel) :
    step machine (cfg 0 D S F 0) = some (cfg (mstate sel) D S F 0) := by
  simp [step, machine, cfg, Configuration.scanned, hF]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem marker_step (sel : Bool) (D S F : List Bool) (pos : ℕ)
    (hD : readTapeBit D pos = true) :
    step machine (cfg (mstate sel) D S F pos) = some (cfg (bstate sel) D S F (pos + 1)) := by
  cases sel <;> simp [step, machine, cfg, Configuration.scanned, hD, mstate, bstate, selOf] <;>
    apply configuration_ext
  all_goals first
    | rfl
    | (funext i; fin_cases i <;> simp [applyAction, HeadMove.apply, mv])

theorem halt_step (sel : Bool) (D S F : List Bool) (pos : ℕ)
    (hD : readTapeBit D pos = false) :
    step machine (cfg (mstate sel) D S F pos) = some (cfg 1 D S F (pos + 1)) := by
  cases sel <;> simp [step, machine, cfg, Configuration.scanned, hD, mstate, selOf] <;>
    apply configuration_ext
  all_goals first
    | rfl
    | (funext i; fin_cases i <;> simp [applyAction, HeadMove.apply, mv])

theorem bit_step (sel d s : Bool) (aD tD aS tS F : List Bool)
    (_hS : aS.length = aD.length)
    (hDr : readTapeBit (aD ++ d :: tD) aD.length = d)
    (hSr : readTapeBit (aS ++ s :: tS) aD.length = s) :
    step machine (cfg (bstate sel) (aD ++ d :: tD) (aS ++ s :: tS) F aD.length) =
      some (cfg (mstate sel) (aD ++ (if sel then s else d) :: tD) (aS ++ s :: tS) F
        (aD.length + 1)) := by
  have wD : ∀ v, writeTapeBit (aD ++ d :: tD) aD.length v = aD ++ v :: tD :=
    fun v => write_mid aD tD d v
  cases sel <;>
    simp [step, machine, cfg, Configuration.scanned, hDr, hSr, mstate, bstate, selOf] <;>
    apply configuration_ext
  all_goals first
    | rfl
    | (funext i; fin_cases i <;> simp [applyAction, HeadMove.apply, mv, wD])

theorem sweep_timed (sel : Bool) :
    ∀ (ds ss : List Bool), ss.length = ds.length →
      ∀ (aD aS : List Bool), aS.length = aD.length → ∀ F : List Bool,
        Timed machine (2 * ds.length + 1)
          (cfg (mstate sel) (aD ++ frame ds) (aS ++ frame ss) F aD.length)
          (cfg 1 (aD ++ frame (if sel then ss else ds)) (aS ++ frame ss) F
            (aD.length + 2 * ds.length + 1)) := by
  intro ds
  induction ds with
  | nil =>
    intro ss hss aD aS haS F
    have hs : ss = [] := List.length_eq_zero_iff.mp (by simpa using hss)
    subst hs
    have hread : readTapeBit (aD ++ frame ([] : List Bool)) aD.length = false := by
      simpa [frame] using Streaming.read_append aD ([] : List Bool) false
    have hstep := halt_step sel (aD ++ frame ([] : List Bool)) (aS ++ frame ([] : List Bool)) F
      aD.length hread
    have h := Timed.single (p := machine) (by cases sel <;> rfl) hstep
    simpa [frame] using h
  | cons d ds ih =>
    intro ss hss aD aS haS F
    cases ss with
    | nil => simp at hss
    | cons s ss =>
      have hss' : ss.length = ds.length := by simpa using hss
      have hDe : aD ++ frame (d :: ds) = (aD ++ [true, d]) ++ frame ds := by
        simp [frame, List.append_assoc]
      have hSe : aS ++ frame (s :: ss) = (aS ++ [true, s]) ++ frame ss := by
        simp [frame, List.append_assoc]
      have hmark : readTapeBit (aD ++ frame (d :: ds)) aD.length = true := by
        simpa [frame, List.append_assoc] using Streaming.read_append aD (d :: frame ds) true
      have hfirst := marker_step sel (aD ++ frame (d :: ds)) (aS ++ frame (s :: ss)) F
        aD.length hmark
      have hreadD : readTapeBit ((aD ++ [true]) ++ d :: frame ds) (aD ++ [true]).length = d :=
        Streaming.read_append (aD ++ [true]) (frame ds) d
      have hreadS : readTapeBit ((aS ++ [true]) ++ s :: frame ss) (aD ++ [true]).length = s := by
        have h := Streaming.read_append (aS ++ [true]) (frame ss) s
        simp only [List.length_append, List.length_cons, List.length_nil, haS] at h ⊢
        exact h
      have hsecond : step machine (cfg (bstate sel) (aD ++ frame (d :: ds))
          (aS ++ frame (s :: ss)) F (aD.length + 1)) =
            some (cfg (mstate sel) ((aD ++ [true, if sel then s else d]) ++ frame ds)
              ((aS ++ [true, s]) ++ frame ss) F (aD.length + 2)) := by
        have h := bit_step sel d s (aD ++ [true]) (frame ds) (aS ++ [true]) (frame ss) F
          (by simp [haS]) hreadD hreadS
        simp only [List.length_append, List.length_cons, List.length_nil] at h
        simpa [frame, List.append_assoc] using h
      have htail := ih ss hss' (aD ++ [true, if sel then s else d]) (aS ++ [true, s])
        (by simp [haS]) F
      have hlen2 : (aD ++ [true, if sel then s else d]).length = aD.length + 2 := by simp
      rw [hlen2] at htail
      have hjoin := (Timed.single (p := machine) (by cases sel <;> rfl) hfirst).trans
        ((Timed.single (p := machine) (by cases sel <;> rfl) hsecond).trans htail)
      have htime : 1 + (1 + (2 * ds.length + 1)) = 2 * (d :: ds).length + 1 := by simp; omega
      have hpos : aD.length + 2 + 2 * ds.length + 1 = aD.length + 2 * (d :: ds).length + 1 := by
        simp; omega
      rw [htime, hpos] at hjoin
      have hif : (if sel then s :: ss else d :: ds) =
          (if sel then s else d) :: (if sel then ss else ds) := by cases sel <;> rfl
      rw [hif]
      simpa [frame, List.append_assoc] using hjoin

theorem select_step (sel : Bool) (ds ss F : List Bool) (hss : ss.length = ds.length)
    (hF : readTapeBit F 0 = sel) :
    Step machine (2 * ds.length + 2) (![0, 0, 0] : Fin 3 → ℕ)
      (![frame ds, frame ss, F] : Fin 3 → List Bool)
      (![2 * ds.length + 1, 2 * ds.length + 1, 0] : Fin 3 → ℕ)
      (![frame (if sel then ss else ds), frame ss, F] : Fin 3 → List Bool) := by
  have hentry := entry_step (frame ds) (frame ss) F sel hF
  have hsweep := sweep_timed sel ds ss hss [] [] rfl F
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at hsweep
  have hall := (Timed.single (p := machine) (by rfl) hentry).trans hsweep
  have htime : 1 + (2 * ds.length + 1) = 2 * ds.length + 2 := by omega
  rw [htime] at hall
  obtain ⟨r, hr, hf, hs⟩ := hall.run (by rfl)
  refine Step.of_run (r := r) ?_ ?_ ?_
  · have hc : cfg 0 (frame ds) (frame ss) F 0 =
        (⟨machine.start, (![0, 0, 0] : Fin 3 → ℕ),
          (![frame ds, frame ss, F] : Fin 3 → List Bool)⟩ : Configuration 3 6) := by
      apply configuration_ext
      · rfl
      · rfl
      · rfl
    rw [hc] at hr
    exact hr
  · rw [hf]; funext i; fin_cases i <;> rfl
  · rw [hf]; funext i; fin_cases i <;> rfl

/-! ## 2. Ports into the seven-tape bank, hoisted out of the nesting -/

def portD : Fin (5 + 1 + 1) := Fin.castAdd 1 (Fin.castAdd 1 0)
def portS : Fin (5 + 1 + 1) := Fin.castAdd 1 (Fin.castAdd 1 1)
def portF : Fin (5 + 1 + 1) := Fin.castAdd 1 (Fin.castAdd 1 3)

def slots : Fin 3 → Fin (5 + 1 + 1) := ![portD, portS, portF]

theorem slots_injective : Function.Injective slots := by
  intro a b h
  have hv := congrArg (fun k : Fin (5 + 1 + 1) => k.val) h
  fin_cases a <;> fin_cases b <;> simp [slots, portD, portS, portF] at hv ⊢

theorem dockH_existing {t u : ℕ} (slot : Fin t → Fin u) (ambient : Fin u → ℕ)
    (local' : Fin t → ℕ) (h : ∀ j, ambient (slot j) = local' j) :
    dockH slot ambient local' = ambient := by
  funext i
  cases hp : RecoveryFocus.pick slot i with
  | none => simp [dockH, hp]
  | some j =>
    have he := RecoveryFocus.slot_of_pick slot hp
    simp only [dockH, hp]
    exact (h j).symm.trans (congrArg ambient he)

noncomputable def loopStart (prime width cap Q : ℕ) (bits : List Bool) :=
  RepeatMachine.cfg 0 (FinalPrimeRow.sourceCfg prime width cap bits 0) Q 1

noncomputable def loopEnd (prime width cap Q : ℕ) (bits : List Bool) :=
  RepeatMachine.cfg 3 (FinalPrimeRow.sourceCfg prime width cap bits Q) Q 1

theorem ambientHeads_port (prime width cap Q : ℕ) (bits : List Bool) (j : Fin 3) :
    (loopEnd prime width cap Q bits).heads (slots j) = (![0, 0, 0] : Fin 3 → ℕ) j := by
  fin_cases j <;> rfl

theorem ambientTapes_port (prime width cap Q : ℕ) (bits : List Bool) (j : Fin 3) :
    (loopEnd prime width cap Q bits).tapes (slots j) =
      (![frame (FinalPrimeRow.stateAt prime width bits Q).1,
        frame (FinalPrimeRow.stateAt prime width bits Q).2.1,
        [(FinalPrimeRow.stateAt prime width bits Q).2.2]] : Fin 3 → List Bool) j := by
  fin_cases j <;> rfl

/-! ## 3. The joined machine -/

noncomputable def whole :=
  Composition.machine (CloseoutRowsDegreeLoop.machine FinalPrimeRow.body)
    (RecoveryFocus.machine slots machine)

def fuel (width Q : ℕ) : ℕ := Q * (FinalPrimeRow.cost width + 3) + 3 + 1 + (2 * width + 2)

theorem whole_step (prime width cap Q : ℕ) (bits : List Bool) (hcap : 2 * width + 2 ≤ cap) :
    Step whole (fuel width Q) (loopStart prime width cap Q bits).heads
      (loopStart prime width cap Q bits).tapes
      (dockH slots (loopEnd prime width cap Q bits).heads
        (![2 * width + 1, 2 * width + 1, 0] : Fin 3 → ℕ))
      (install slots (loopEnd prime width cap Q bits).tapes
        (![frame (FinalPrimeRow.residueWord (FinalPrimeRow.stateAt prime width bits Q)),
          frame (FinalPrimeRow.stateAt prime width bits Q).2.1,
          [(FinalPrimeRow.stateAt prime width bits Q).2.2]] : Fin 3 → List Bool)) := by
  obtain ⟨r, hr, hf, hs⟩ := CloseoutRowsDegreeLoop.loop_run FinalPrimeRow.body
    (fun j _ => FinalPrimeRow.sourceCfg prime width cap bits j) (fun _ => [])
    (FinalPrimeRow.cost width) Q (fun _ _ _ => rfl)
    (fun j _ _ => by
      obtain ⟨rr, h1, h2, h3, h4⟩ := FinalPrimeRow.body_supplier prime width cap bits j hcap
      exact ⟨rr, h1, h2, h3, h4⟩) []
  have hcfg : (⟨(CloseoutRowsDegreeLoop.machine FinalPrimeRow.body).start,
      (loopStart prime width cap Q bits).heads, (loopStart prime width cap Q bits).tapes⟩ :
        Configuration (5 + 1 + 1) _) =
      RepeatMachine.cfg 0 (FinalPrimeRow.sourceCfg prime width cap bits 0) Q 1 := by
    apply configuration_ext
    · rfl
    · rfl
    · rfl
  rw [← hcfg] at hr
  have hloop : Step (CloseoutRowsDegreeLoop.machine FinalPrimeRow.body)
      (Q * (FinalPrimeRow.cost width + 3) + 3) (loopStart prime width cap Q bits).heads
      (loopStart prime width cap Q bits).tapes (loopEnd prime width cap Q bits).heads
      (loopEnd prime width cap Q bits).tapes :=
    Step.of_run hr (by rw [hf]; rfl) (by rw [hf]; rfl)
  have hlenT := (FinalPrimeRow.stateAt_length prime width bits Q).1
  have hlenU := (FinalPrimeRow.stateAt_length prime width bits Q).2
  have hF : readTapeBit [(FinalPrimeRow.stateAt prime width bits Q).2.2] 0 =
      (FinalPrimeRow.stateAt prime width bits Q).2.2 := rfl
  have hsel := select_step (FinalPrimeRow.stateAt prime width bits Q).2.2
    (FinalPrimeRow.stateAt prime width bits Q).1 (FinalPrimeRow.stateAt prime width bits Q).2.1
    [(FinalPrimeRow.stateAt prime width bits Q).2.2] (by rw [hlenU, hlenT]) hF
  rw [hlenT] at hsel
  have hfoc := hsel.focus slots slots_injective (loopEnd prime width cap Q bits).heads
    (loopEnd prime width cap Q bits).tapes
  rw [dockH_existing slots _ _ (ambientHeads_port prime width cap Q bits),
    install_existing slots _ _ (ambientTapes_port prime width cap Q bits)] at hfoc
  have hres : (if (FinalPrimeRow.stateAt prime width bits Q).2.2 then
      (FinalPrimeRow.stateAt prime width bits Q).2.1
    else (FinalPrimeRow.stateAt prime width bits Q).1) =
      FinalPrimeRow.residueWord (FinalPrimeRow.stateAt prime width bits Q) := rfl
  rw [hres] at hfoc
  exact hloop.seq hfoc

/-! ## 4. One prime row, residue delivered as a single framed word -/

theorem fuel_value (width Q : ℕ) : fuel width Q = Q * (4 * width + 9) + 2 * width + 6 := by
  unfold fuel FinalPrimeRow.cost
  ring

end NearCubicWires.RepairOrdinary.FinalPrimeResidue

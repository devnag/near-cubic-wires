import Proof.CaseAnalysis.RowsDegreeLoop
import Proof.MachineModel.Runs
import Proof.Rows.FinalWalkStep

namespace NearCubicWires.RepairOrdinary.FinalPrimeRow
open LocalBitMultitape RecoveryExecution RadixSemantics ExtDecompositionBatch
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## 1. Finite control

State `0` reads the flag cell and the target bit, state `1` halts.  States
`2..9` scan a frame marker and `10..17` scan a bit; in both groups the code
carries the latched selector, the delayed residue bit and the running carry. -/

def markerState (sel buf car : Bool) : Fin 18 :=
  if sel then (if buf then (if car then 9 else 8) else (if car then 7 else 6))
  else (if buf then (if car then 5 else 4) else (if car then 3 else 2))

def bitState (sel buf car : Bool) : Fin 18 :=
  if sel then (if buf then (if car then 17 else 16) else (if car then 15 else 14))
  else (if buf then (if car then 13 else 12) else (if car then 11 else 10))

def selOf (q : Fin 18) : Bool := decide (4 ≤ (q.val - 2) % 8)
def bufOf (q : Fin 18) : Bool := decide (2 ≤ (q.val - 2) % 4)
def carOf (q : Fin 18) : Bool := decide ((q.val - 2) % 2 = 1)


/-- Tapes: `0 = T`, `1 = U`, `2 = P`, `3 = F` (one cell), `4 = N`. -/
def wordMove : Fin 5 → HeadMove := fun i => if i.val ≤ 2 then .right else .stay

def machine : Machine 5 18 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q scanned =>
    if q.val = 0 then
      some ⟨markerState (scanned 3) (scanned 4) true, fun _ => none,
        fun i => if i.val = 4 then .right else .stay⟩
    else if q.val = 1 then none
    else if q.val < 10 then
      (if scanned 0 then
        some ⟨bitState (selOf q) (bufOf q) (carOf q), fun _ => none, wordMove⟩
      else
        some ⟨1, fun i => if i.val = 3 then some (carOf q) else none, wordMove⟩)
    else
      some ⟨markerState (selOf q) (if selOf q then scanned 1 else scanned 0)
          (Add.carry (bufOf q) (!scanned 2) (carOf q)),
        fun i => if i.val = 0 then some (bufOf q)
          else if i.val = 1 then some (Add.bit (bufOf q) (!scanned 2) (carOf q)) else none,
        wordMove⟩

def config (q : Fin 18) (T U P F N : List Bool) (pos npos : ℕ) : Configuration 5 18 :=
  ⟨q, ![pos, pos, pos, 0, npos], ![T, U, P, F, N]⟩

theorem write_mid (pre tail : List Bool) (old v : Bool) :
    writeTapeBit (pre ++ old :: tail) pre.length v = pre ++ v :: tail := by
  induction pre with
  | nil => rfl
  | cons b pre ih => simpa [writeTapeBit] using congrArg (List.cons b) ih

/-! ## 2. The four local transitions -/

theorem entry_step (T U P F N : List Bool) (npos : ℕ) (sel b : Bool)
    (hF : readTapeBit F 0 = sel) (hN : readTapeBit N npos = b) :
    step machine (config 0 T U P F N 0 npos) =
      some (config (markerState sel b true) T U P F N 0 (npos + 1)) := by
  simp [step, machine, config, Configuration.scanned, hF, hN]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem marker_step (sel buf car : Bool) (aT tT U P F N : List Bool) (npos : ℕ)
    (hT : readTapeBit (aT ++ true :: tT) aT.length = true) :
    step machine (config (markerState sel buf car) (aT ++ true :: tT) U P F N aT.length npos) =
      some (config (bitState sel buf car) (aT ++ true :: tT) U P F N (aT.length + 1) npos) := by
  cases sel <;> cases buf <;> cases car <;>
    simp [step, machine, config, Configuration.scanned, hT, markerState, bitState,
      selOf, bufOf, carOf] <;>
    apply configuration_ext
  all_goals first
    | rfl
    | (funext i; fin_cases i <;> simp [applyAction, HeadMove.apply, wordMove])

theorem halt_step (sel buf car : Bool) (aT tT U P F N : List Bool) (npos : ℕ)
    (hT : readTapeBit (aT ++ false :: tT) aT.length = false) :
    step machine (config (markerState sel buf car) (aT ++ false :: tT) U P F N aT.length npos) =
      some (config 1 (aT ++ false :: tT) U P (writeTapeBit F 0 car) N (aT.length + 1) npos) := by
  cases sel <;> cases buf <;> cases car <;>
    simp [step, machine, config, Configuration.scanned, hT, markerState,
      selOf, bufOf, carOf] <;>
    apply configuration_ext
  all_goals first
    | rfl
    | (funext i; fin_cases i <;> simp [applyAction, HeadMove.apply, wordMove])

theorem bit_step (sel buf car t u pp : Bool) (aT tT aU tU aP tP F N : List Bool) (npos : ℕ)
    (hU : aU.length = aT.length) (_hP : aP.length = aT.length)
    (hT : readTapeBit (aT ++ t :: tT) aT.length = t)
    (hUr : readTapeBit (aU ++ u :: tU) aT.length = u)
    (hPr : readTapeBit (aP ++ pp :: tP) aT.length = pp) :
    step machine (config (bitState sel buf car) (aT ++ t :: tT) (aU ++ u :: tU)
        (aP ++ pp :: tP) F N aT.length npos) =
      some (config (markerState sel (if sel then u else t) (Add.carry buf (!pp) car))
        (aT ++ buf :: tT) (aU ++ Add.bit buf (!pp) car :: tU) (aP ++ pp :: tP) F N
        (aT.length + 1) npos) := by
  have wT : ∀ v, writeTapeBit (aT ++ t :: tT) aT.length v = aT ++ v :: tT :=
    fun v => write_mid aT tT t v
  have wU : ∀ v, writeTapeBit (aU ++ u :: tU) aT.length v = aU ++ v :: tU := by
    intro v; rw [← hU]; exact write_mid aU tU u v
  cases sel <;> cases buf <;> cases car <;>
    simp [step, machine, config, Configuration.scanned, hT, hUr, hPr, markerState,
      bitState, selOf, bufOf, carOf] <;>
    apply configuration_ext
  all_goals first
    | rfl
    | (funext i; fin_cases i <;>
        simp [applyAction, HeadMove.apply, wordMove, wT, wU])

/-! ## 3. One sweep -/

def negWord (ps : List Bool) : List Bool := ps.map (fun b => !b)

theorem sweep_timed (sel : Bool) :
    ∀ (ts us ps : List Bool), us.length = ts.length → ps.length = ts.length →
      ∀ (aT aU aP : List Bool), aU.length = aT.length → aP.length = aT.length →
        ∀ (F N : List Bool) (npos : ℕ) (buf car : Bool),
          Timed machine (2 * ts.length + 1)
            (config (markerState sel buf car) (aT ++ frame ts) (aU ++ frame us)
              (aP ++ frame ps) F N aT.length npos)
            (config 1 (aT ++ frame (FinalWalkStep.shift false buf (if sel then us else ts)))
              (aU ++ frame (Add.sum (FinalWalkStep.shift false buf (if sel then us else ts))
                (negWord ps) car))
              (aP ++ frame ps)
              (writeTapeBit F 0 (Add.overflow (FinalWalkStep.shift false buf
                (if sel then us else ts)) (negWord ps) car))
              N (aT.length + 2 * ts.length + 1) npos) := by
  intro ts
  induction ts with
  | nil =>
    intro us ps hus hps aT aU aP haU haP F N npos buf car
    have hu : us = [] := List.length_eq_zero_iff.mp (by simpa using hus)
    have hp : ps = [] := List.length_eq_zero_iff.mp (by simpa using hps)
    subst hu; subst hp
    have hread : readTapeBit (aT ++ frame ([] : List Bool)) aT.length = false := by
      simpa [frame] using Streaming.read_append aT ([] : List Bool) false
    have hstep := halt_step sel buf car aT [] (aU ++ frame ([] : List Bool))
      (aP ++ frame ([] : List Bool)) F N npos (by simpa [frame] using hread)
    have h := Timed.single (p := machine)
      (by cases sel <;> cases buf <;> cases car <;> rfl) hstep
    simpa [frame, FinalWalkStep.shift, Add.sum, Add.overflow, negWord] using h
  | cons t ts ih =>
    intro us ps hus hps aT aU aP haU haP F N npos buf car
    cases us with
    | nil => simp at hus
    | cons u us =>
      cases ps with
      | nil => simp at hps
      | cons pp ps =>
        have hus' : us.length = ts.length := by simpa using hus
        have hps' : ps.length = ts.length := by simpa using hps
        have hTe : aT ++ frame (t :: ts) = (aT ++ [true, t]) ++ frame ts := by
          simp [frame, List.append_assoc]
        have hUe : aU ++ frame (u :: us) = (aU ++ [true, u]) ++ frame us := by
          simp [frame, List.append_assoc]
        have hPe : aP ++ frame (pp :: ps) = (aP ++ [true, pp]) ++ frame ps := by
          simp [frame, List.append_assoc]
        have hmark : readTapeBit (aT ++ frame (t :: ts)) aT.length = true := by
          simpa [frame, List.append_assoc] using
            Streaming.read_append aT (t :: frame ts) true
        have hfirst : step machine (config (markerState sel buf car) (aT ++ frame (t :: ts))
            (aU ++ frame (u :: us)) (aP ++ frame (pp :: ps)) F N aT.length npos) =
              some (config (bitState sel buf car) (aT ++ frame (t :: ts))
                (aU ++ frame (u :: us)) (aP ++ frame (pp :: ps)) F N (aT.length + 1) npos) := by
          have h := marker_step sel buf car aT (t :: frame ts) (aU ++ frame (u :: us))
            (aP ++ frame (pp :: ps)) F N npos (by simpa [frame, List.append_assoc] using hmark)
          simpa [frame, List.append_assoc] using h
        have hreadT : readTapeBit ((aT ++ [true]) ++ t :: frame ts) (aT ++ [true]).length = t :=
          Streaming.read_append (aT ++ [true]) (frame ts) t
        have hreadU : readTapeBit ((aU ++ [true]) ++ u :: frame us) (aT ++ [true]).length = u := by
          have h := Streaming.read_append (aU ++ [true]) (frame us) u
          simp only [List.length_append, List.length_cons, List.length_nil, haU] at h ⊢
          exact h
        have hreadP : readTapeBit ((aP ++ [true]) ++ pp :: frame ps) (aT ++ [true]).length = pp := by
          have h := Streaming.read_append (aP ++ [true]) (frame ps) pp
          simp only [List.length_append, List.length_cons, List.length_nil, haP] at h ⊢
          exact h
        have hsecond : step machine (config (bitState sel buf car) (aT ++ frame (t :: ts))
            (aU ++ frame (u :: us)) (aP ++ frame (pp :: ps)) F N (aT.length + 1) npos) =
              some (config (markerState sel (if sel then u else t) (Add.carry buf (!pp) car))
                ((aT ++ [true, buf]) ++ frame ts)
                ((aU ++ [true, Add.bit buf (!pp) car]) ++ frame us)
                ((aP ++ [true, pp]) ++ frame ps) F N (aT.length + 2) npos) := by
          have h := bit_step sel buf car t u pp (aT ++ [true]) (frame ts) (aU ++ [true]) (frame us)
            (aP ++ [true]) (frame ps) F N npos (by simp [haU]) (by simp [haP])
            hreadT hreadU hreadP
          simp only [List.length_append, List.length_cons, List.length_nil] at h
          simpa [frame, List.append_assoc] using h
        have htail := ih us ps hus' hps' (aT ++ [true, buf]) (aU ++ [true, Add.bit buf (!pp) car])
          (aP ++ [true, pp]) (by simp [haU]) (by simp [haP]) F N npos (if sel then u else t)
          (Add.carry buf (!pp) car)
        have hlen2 : (aT ++ [true, buf]).length = aT.length + 2 := by simp
        rw [hlen2] at htail
        have hjoin := (Timed.single (p := machine)
            (by cases sel <;> cases buf <;> cases car <;> rfl) hfirst).trans
          ((Timed.single (p := machine)
            (by cases sel <;> cases buf <;> cases car <;> rfl) hsecond).trans htail)
        have htime : 1 + (1 + (2 * ts.length + 1)) = 2 * (t :: ts).length + 1 := by
          simp; omega
        have hpos : aT.length + 2 + 2 * ts.length + 1 = aT.length + 2 * (t :: ts).length + 1 := by
          simp; omega
        rw [htime, hpos] at hjoin
        have hif : (if sel then u :: us else t :: ts) =
            (if sel then u else t) :: (if sel then us else ts) := by cases sel <;> rfl
        rw [hif]
        simpa [FinalWalkStep.shift_cons, Add.sum, Add.overflow, negWord, frame,
          List.append_assoc] using hjoin

/-! ## 4. The whole pass, including the entry read -/

theorem pass_run (sel b : Bool) (ts us ps F N : List Bool) (npos : ℕ)
    (hus : us.length = ts.length) (hps : ps.length = ts.length)
    (hF : readTapeBit F 0 = sel) (hN : readTapeBit N npos = b) :
    ∃ r : ExecutionReceipt 5 18,
      runFrom machine (2 * ts.length + 2)
          ⟨machine.start, ![0, 0, 0, 0, npos], ![frame ts, frame us, frame ps, F, N]⟩ =
        some r ∧
      r.steps = 2 * ts.length + 2 ∧
      r.final.heads = ![2 * ts.length + 1, 2 * ts.length + 1, 2 * ts.length + 1, 0, npos + 1] ∧
      r.final.tapes =
        ![frame (FinalWalkStep.shift false b (if sel then us else ts)),
          frame (Add.sum (FinalWalkStep.shift false b (if sel then us else ts)) (negWord ps) true),
          frame ps,
          writeTapeBit F 0 (Add.overflow (FinalWalkStep.shift false b
            (if sel then us else ts)) (negWord ps) true), N] := by
  have hentry := entry_step (frame ts) (frame us) (frame ps) F N npos sel b hF hN
  have hsweep := sweep_timed sel ts us ps hus hps [] [] [] rfl rfl F N (npos + 1) b true
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at hsweep
  have hall := (Timed.single (p := machine) (by rfl) hentry).trans hsweep
  have htime : 1 + (2 * ts.length + 1) = 2 * ts.length + 2 := by omega
  rw [htime] at hall
  obtain ⟨r, hr, hf, hs⟩ := hall.run (by rfl)
  refine ⟨r, ?_, hs, ?_, ?_⟩
  · have hcfg : config 0 (frame ts) (frame us) (frame ps) F N 0 npos =
        (⟨machine.start, ![0, 0, 0, 0, npos], ![frame ts, frame us, frame ps, F, N]⟩ :
          Configuration 5 18) := by
      apply configuration_ext
      · rfl
      · rfl
      · rfl
    rw [hcfg] at hr
    exact hr
  · rw [hf]; funext i; fin_cases i <;> rfl
  · rw [hf]; funext i; fin_cases i <;> rfl

/-! ## 5. Exact arithmetic of one sweep -/

def residueOf (state : List Bool × List Bool × Bool) : ℕ :=
  value (if state.2.2 then state.2.1 else state.1)

def nextState (prime width : ℕ) (b : Bool) (state : List Bool × List Bool × Bool) :
    List Bool × List Bool × Bool :=
  let nt := FinalWalkStep.shift false b (if state.2.2 then state.2.1 else state.1)
  (nt, Add.sum nt (negWord (SignedSortKey.binary width prime)) true,
    Add.overflow nt (negWord (SignedSortKey.binary width prime)) true)

theorem negWord_value (ps : List Bool) : value (negWord ps) + value ps + 1 = 2 ^ ps.length := by
  simpa [negWord] using FinalWalkStep.value_map_not ps

@[simp] theorem negWord_length (ps : List Bool) : (negWord ps).length = ps.length := by
  simp [negWord]

theorem shift_value_exact (b : Bool) (s : List Bool) (hs : b.toNat + 2 * value s < 2 ^ s.length) :
    value (FinalWalkStep.shift false b s) = b.toNat + 2 * value s := by
  have hmod := FinalWalkStep.shift_modEq b s
  have hlt : value (FinalWalkStep.shift false b s) < 2 ^ s.length := by
    have h := value_lt (FinalWalkStep.shift false b s)
    rwa [FinalWalkStep.shift_length] at h
  have h1 : value (FinalWalkStep.shift false b s) % 2 ^ s.length =
      (b.toNat + 2 * value s) % 2 ^ s.length := hmod
  rwa [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hs] at h1

/-- One sweep advances the Horner residue by one target bit. -/
theorem residue_next (prime width : ℕ) (b : Bool) (state : List Bool × List Bool × Bool)
    (h1 : state.1.length = width) (h2 : state.2.1.length = width)
    (_hp0 : 0 < prime) (hp : 2 * prime ≤ 2 ^ width) (hres : residueOf state < prime) :
    residueOf (nextState prime width b state) = (2 * residueOf state + b.toNat) % prime ∧
      (nextState prime width b state).1.length = width ∧
      (nextState prime width b state).2.1.length = width := by
  set s := (if state.2.2 then state.2.1 else state.1) with hsdef
  have hslen : s.length = width := by rw [hsdef]; split <;> assumption
  have hsval : value s = residueOf state := rfl
  set nt := FinalWalkStep.shift false b s with hntdef
  have hntlen : nt.length = width := by rw [hntdef, FinalWalkStep.shift_length, hslen]
  have hfit : b.toNat + 2 * value s < 2 ^ width := by
    have hb : b.toNat ≤ 1 := by cases b <;> simp
    rw [hsval]
    omega
  have hntval : value nt = b.toNat + 2 * residueOf state := by
    rw [hntdef, shift_value_exact b s (by rw [hslen]; exact hfit), hsval]
  set np := negWord (SignedSortKey.binary width prime) with hnpdef
  have hnplen : np.length = width := by rw [hnpdef, negWord_length]; simp
  have hnpval : value np + prime + 1 = 2 ^ width := by
    have h := negWord_value (SignedSortKey.binary width prime)
    rw [← hnpdef, SignedSortKey.binary_length,
      SignedSortKey.binary_value width prime (by omega)] at h
    exact h
  have hw : nt.length = np.length := by rw [hntlen, hnplen]
  have hsum := Add.sum_value nt np true hw
  rw [hntlen] at hsum
  have hsumlt : value (Add.sum nt np true) < 2 ^ width := by
    have h := value_lt (Add.sum nt np true)
    rwa [Add.sum_length nt np true hw, hntlen] at h
  have hsumlen : (Add.sum nt np true).length = width := by
    rw [Add.sum_length nt np true hw, hntlen]
  refine ⟨?_, by simpa [nextState, hntdef, hsdef] using hntlen,
    by simpa [nextState, hntdef, hsdef, hnpdef] using hsumlen⟩
  have hgoal : residueOf (nextState prime width b state) =
      (if Add.overflow nt np true then value (Add.sum nt np true) else value nt) := by
    simp only [residueOf, nextState, ← hsdef, ← hntdef, ← hnpdef]
    split <;> rfl
  have hb : b.toNat ≤ 1 := by cases b <;> simp
  have htv : value nt = 2 * residueOf state + b.toNat := by rw [hntval]; omega
  cases hov : Add.overflow nt np true with
  | false =>
    rw [hov, Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.add_zero] at hsum
    rw [hgoal, hov, if_neg (by simp), ← htv]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  | true =>
    rw [hov, Bool.toNat_true, Nat.mul_one] at hsum
    have hge : prime ≤ value nt := by omega
    have heq : value (Add.sum nt np true) = value nt - prime := by omega
    have hlt2 : value nt < 2 * prime := by rw [htv]; omega
    rw [hgoal, hov, if_pos rfl, heq, ← htv,
      Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]

/-! ## 6. The driven loop: the whole residue of one target modulo one prime -/

def selected : Fin 5 → Bool := ![true, true, true, false, false]

def body := MaskedReset.machine machine selected

def cost (width : ℕ) : ℕ := 2 * (2 * width + 2) + 2

def stateAt (prime width : ℕ) (bits : List Bool) : ℕ → List Bool × List Bool × Bool
  | 0 => (SignedSortKey.binary width 0, SignedSortKey.binary width 0, false)
  | j + 1 => nextState prime width (bits.getD j false) (stateAt prime width bits j)

def horner (bits : List Bool) (j : ℕ) : ℕ :=
  (List.range j).foldl (fun acc i => 2 * acc + (bits.getD i false).toNat) 0

theorem horner_succ (bits : List Bool) (j : ℕ) :
    horner bits (j + 1) = 2 * horner bits j + (bits.getD j false).toNat := by
  simp [horner, List.range_succ]

theorem nextState_length (prime width : ℕ) (b : Bool) (st : List Bool × List Bool × Bool)
    (h1 : st.1.length = width) (h2 : st.2.1.length = width) :
    (nextState prime width b st).1.length = width ∧
      (nextState prime width b st).2.1.length = width := by
  have hs : (if st.2.2 then st.2.1 else st.1).length = width := by split <;> assumption
  have hnt : (FinalWalkStep.shift false b (if st.2.2 then st.2.1 else st.1)).length = width := by
    rw [FinalWalkStep.shift_length, hs]
  have hw : (FinalWalkStep.shift false b (if st.2.2 then st.2.1 else st.1)).length =
      (negWord (SignedSortKey.binary width prime)).length := by
    rw [hnt, negWord_length, SignedSortKey.binary_length]
  refine ⟨hnt, ?_⟩
  show (Add.sum (FinalWalkStep.shift false b (if st.2.2 then st.2.1 else st.1))
    (negWord (SignedSortKey.binary width prime)) true).length = width
  rw [Add.sum_length _ _ _ hw, hnt]

theorem stateAt_length (prime width : ℕ) (bits : List Bool) (j : ℕ) :
    (stateAt prime width bits j).1.length = width ∧
      (stateAt prime width bits j).2.1.length = width := by
  induction j with
  | zero => simp [stateAt]
  | succ j ih => exact nextState_length prime width _ _ ih.1 ih.2

theorem stateAt_residue (prime width : ℕ) (bits : List Bool) (j : ℕ)
    (hp0 : 0 < prime) (hp : 2 * prime ≤ 2 ^ width) :
    residueOf (stateAt prime width bits j) = horner bits j % prime := by
  induction j with
  | zero =>
    have h2 : (0 : ℕ) < 2 ^ width := by positivity
    simp [stateAt, residueOf, horner, SignedSortKey.binary_value width 0 h2]
  | succ j ih =>
    have hlen := stateAt_length prime width bits j
    have hres : residueOf (stateAt prime width bits j) < prime := by
      rw [ih]; exact Nat.mod_lt _ hp0
    have hstep := (residue_next prime width (bits.getD j false) (stateAt prime width bits j)
      hlen.1 hlen.2 hp0 hp hres).1
    rw [show stateAt prime width bits (j + 1) =
      nextState prime width (bits.getD j false) (stateAt prime width bits j) from rfl,
      hstep, ih, horner_succ]
    exact ((Nat.mod_modEq (horner bits j) prime).mul_left 2).add_right
      ((bits.getD j false).toNat)

noncomputable def sourceCfg (prime width cap : ℕ) (bits : List Bool) (j : ℕ) :
    Configuration (5 + 1) (18 + 2) :=
  ⟨body.start,
    Fin.addCases (motive := fun _ => ℕ) (![0, 0, 0, 0, j] : Fin 5 → ℕ) (fun _ : Fin 1 => 0),
    Fin.addCases (motive := fun _ => List Bool)
      (![frame (stateAt prime width bits j).1, frame (stateAt prime width bits j).2.1,
        frame (SignedSortKey.binary width prime), [(stateAt prime width bits j).2.2],
        bits] : Fin 5 → List Bool)
      (fun _ : Fin 1 => List.replicate cap false)⟩

theorem body_supplier (prime width cap : ℕ) (bits : List Bool) (j : ℕ)
    (hcap : 2 * width + 2 ≤ cap) :
    ∃ r, runFrom body (cost width) (sourceCfg prime width cap bits j) = some r ∧
      r.final.heads = (sourceCfg prime width cap bits (j + 1)).heads ∧
      r.final.tapes = (sourceCfg prime width cap bits (j + 1)).tapes ∧ r.steps ≤ cost width := by
  obtain ⟨hT, hU⟩ := stateAt_length prime width bits j
  have hps : (SignedSortKey.binary width prime).length = (stateAt prime width bits j).1.length := by
    rw [SignedSortKey.binary_length, hT]
  have hF : readTapeBit [(stateAt prime width bits j).2.2] 0 =
      (stateAt prime width bits j).2.2 := rfl
  have hN : readTapeBit bits j = bits.getD j false := rfl
  obtain ⟨raw, hraw, hsteps, hheads, htapes⟩ :=
    pass_run (stateAt prime width bits j).2.2 (bits.getD j false)
      (stateAt prime width bits j).1 (stateAt prime width bits j).2.1
      (SignedSortKey.binary width prime) [(stateAt prime width bits j).2.2] bits j
      (by rw [hU, hT]) hps hF hN
  rw [hT] at hraw hsteps hheads
  have hstep : Step machine (2 * width + 2) (![0, 0, 0, 0, j] : Fin 5 → ℕ)
      (![frame (stateAt prime width bits j).1, frame (stateAt prime width bits j).2.1,
        frame (SignedSortKey.binary width prime), [(stateAt prime width bits j).2.2],
        bits] : Fin 5 → List Bool)
      (![2 * width + 1, 2 * width + 1, 2 * width + 1, 0, j + 1] : Fin 5 → ℕ)
      (![frame (stateAt prime width bits (j + 1)).1,
        frame (stateAt prime width bits (j + 1)).2.1,
        frame (SignedSortKey.binary width prime), [(stateAt prime width bits (j + 1)).2.2],
        bits] : Fin 5 → List Bool) := by
    refine Step.of_run (r := raw) hraw hheads ?_
    rw [htapes]
    funext i
    fin_cases i <;> rfl
  obtain ⟨r, hr, hh, ht, hs⟩ := hstep.mask selected
    (by intro i; fin_cases i <;> simp [selected]) hcap
  refine ⟨r, hr, ?_, ht, hs⟩
  have hheadsEq : (sourceCfg prime width cap bits (j + 1)).heads =
      Fin.addCases (motive := fun _ => ℕ)
        (fun i => if selected i then 0
          else (![2 * width + 1, 2 * width + 1, 2 * width + 1, 0, j + 1] : Fin 5 → ℕ) i)
        (fun _ : Fin 1 => 0) := by
    show Fin.addCases (motive := fun _ => ℕ) (![0, 0, 0, 0, j + 1] : Fin 5 → ℕ)
      (fun _ : Fin 1 => 0) = _
    congr 1
    funext k
    fin_cases k <;> simp [selected]
  rw [hh]
  exact hheadsEq.symm


/-! ## 7. One prime row: the residue of a canonical target modulo one prime

`primesUpTo`'s members are the row index of Appendix A.13.  For such a prime,
`primeWidth` is the `modulusDigitCount`-plus-one word width the sweep needs,
`targetBits` is the MSB-first digit stream of the canonical target, and the
driven loop below reads the residue off in `K * (4 * primeWidth + 9) + 3`
ordinary steps. -/

def residueWord (st : List Bool × List Bool × Bool) : List Bool :=
  if st.2.2 then st.2.1 else st.1

theorem residueOf_word (st : List Bool × List Bool × Bool) :
    residueOf st = value (residueWord st) := rfl

theorem horner_take (bits : List Bool) :
    ∀ j, j ≤ bits.length → horner bits j = value ((bits.take j).reverse) := by
  intro j
  induction j with
  | zero => intro _; simp [horner, value]
  | succ j ih =>
    intro hj
    have hjlt : j < bits.length := by omega
    have hget : bits.getD j false = bits[j] := by
      simp [List.getD_eq_getElem?_getD, hjlt]
    have htake : bits.take (j + 1) = bits.take j ++ [bits[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hjlt]
      rfl
    rw [horner_succ, ih (by omega), htake, List.reverse_append, hget]
    simp [value]
    ring

end NearCubicWires.RepairOrdinary.FinalPrimeRow

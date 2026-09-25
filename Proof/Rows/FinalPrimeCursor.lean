import Proof.Rows.FinalPrimeNegate

namespace NearCubicWires.RepairOrdinary.FinalPrimeCursor
open LocalBitMultitape RecoveryExecution RadixSemantics ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## 1. Clearing a framed word -/

def clearMachine : Machine 1 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q scanned =>
    if q.val = 0 then
      (if scanned 0 then some ⟨1, fun _ => none, fun _ => .right⟩
        else some ⟨2, fun _ => none, fun _ => .right⟩)
    else if q.val = 1 then some ⟨0, fun _ => some false, fun _ => .right⟩
    else none

def ccfg (q : Fin 3) (W : List Bool) (pos : ℕ) : Configuration 1 3 :=
  ⟨q, fun _ => pos, fun _ => W⟩

theorem write_mid (pre tail : List Bool) (old v : Bool) :
    writeTapeBit (pre ++ old :: tail) pre.length v = pre ++ v :: tail := by
  induction pre with
  | nil => rfl
  | cons b pre ih => simpa [writeTapeBit] using congrArg (List.cons b) ih

theorem clear_marker (W : List Bool) (pos : ℕ) (hW : readTapeBit W pos = true) :
    step clearMachine (ccfg 0 W pos) = some (ccfg 1 W (pos + 1)) := by
  simp [step, clearMachine, ccfg, Configuration.scanned, hW]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · funext i; simp [applyAction]

theorem clear_halt (W : List Bool) (pos : ℕ) (hW : readTapeBit W pos = false) :
    step clearMachine (ccfg 0 W pos) = some (ccfg 2 W (pos + 1)) := by
  simp [step, clearMachine, ccfg, Configuration.scanned, hW]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · funext i; simp [applyAction]

theorem clear_bit (b : Bool) (aW tW : List Bool) :
    step clearMachine (ccfg 1 (aW ++ b :: tW) aW.length) =
      some (ccfg 0 (aW ++ false :: tW) (aW.length + 1)) := by
  simp [step, clearMachine, ccfg]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · funext i; simp [applyAction, write_mid]

theorem clear_timed :
    ∀ (ws aW : List Bool),
      Timed clearMachine (2 * ws.length + 1) (ccfg 0 (aW ++ frame ws) aW.length)
        (ccfg 2 (aW ++ frame (List.replicate ws.length false)) (aW.length + 2 * ws.length + 1)) := by
  intro ws
  induction ws with
  | nil =>
    intro aW
    have hread : readTapeBit (aW ++ frame ([] : List Bool)) aW.length = false := by
      simpa [frame] using Streaming.read_append aW ([] : List Bool) false
    have h := Timed.single (p := clearMachine) (by rfl)
      (clear_halt (aW ++ frame ([] : List Bool)) aW.length hread)
    simpa [frame] using h
  | cons b ws ih =>
    intro aW
    have hmark : readTapeBit (aW ++ frame (b :: ws)) aW.length = true := by
      simpa [frame, List.append_assoc] using Streaming.read_append aW (b :: frame ws) true
    have hfirst := clear_marker (aW ++ frame (b :: ws)) aW.length hmark
    have hsecond : step clearMachine (ccfg 1 (aW ++ frame (b :: ws)) (aW.length + 1)) =
        some (ccfg 0 ((aW ++ [true, false]) ++ frame ws) (aW.length + 2)) := by
      have h := clear_bit b (aW ++ [true]) (frame ws)
      simp only [List.length_append, List.length_cons, List.length_nil] at h
      simpa [frame, List.append_assoc] using h
    have htail := ih (aW ++ [true, false])
    have hlen : (aW ++ [true, false]).length = aW.length + 2 := by simp
    rw [hlen] at htail
    have hjoin := (Timed.single (p := clearMachine) (by rfl) hfirst).trans
      ((Timed.single (p := clearMachine) (by rfl) hsecond).trans htail)
    have htime : 1 + (1 + (2 * ws.length + 1)) = 2 * (b :: ws).length + 1 := by simp; omega
    have hpos : aW.length + 2 + 2 * ws.length + 1 = aW.length + 2 * (b :: ws).length + 1 := by
      simp; omega
    rw [htime, hpos] at hjoin
    simpa [List.replicate_succ, frame, List.append_assoc] using hjoin

theorem binary_zero (width : ℕ) : SignedSortKey.binary width 0 = List.replicate width false := by
  induction width with
  | zero => rfl
  | succ width ih => simp [SignedSortKey.binary, List.replicate_succ, ih]

/-- One pass re-initialises a framed word to the encoded zero. -/
theorem clear_step (ws : List Bool) :
    Step clearMachine (2 * ws.length + 1) (fun _ => 0) (fun _ => frame ws) (fun _ => 2 * ws.length + 1)
      (fun _ => frame (SignedSortKey.binary ws.length 0)) := by
  have h := clear_timed ws []
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at h
  obtain ⟨r, hr, hf, hs⟩ := h.run (by rfl)
  rw [binary_zero]
  refine Step.of_run (r := r) ?_ ?_ ?_
  · have hc : ccfg 0 (frame ws) 0 =
        (⟨clearMachine.start, (fun _ => 0), (fun _ => frame ws)⟩ : Configuration 1 3) := by
      apply configuration_ext
      · rfl
      · rfl
      · rfl
    rw [hc] at hr
    exact hr
  · rw [hf]; rfl
  · rw [hf]; rfl

/-! ## 2. Incrementing a framed word -/

def mstate (c : Bool) : Fin 5 := if c then 1 else 0
def bstate (c : Bool) : Fin 5 := if c then 3 else 2
def carOf (q : Fin 5) : Bool := decide (q.val % 2 = 1)


def incrMachine : Machine 1 5 where
  descriptionBits := 0
  start := mstate true
  halted := fun q => q.val == 4
  rule := fun q scanned =>
    if q.val < 2 then
      (if scanned 0 then some ⟨bstate (carOf q), fun _ => none, fun _ => .right⟩
        else some ⟨4, fun _ => none, fun _ => .right⟩)
    else if q.val < 4 then
      some ⟨mstate (scanned 0 && carOf q), fun _ => some (xor (scanned 0) (carOf q)),
        fun _ => .right⟩
    else none

def icfg (q : Fin 5) (W : List Bool) (pos : ℕ) : Configuration 1 5 :=
  ⟨q, fun _ => pos, fun _ => W⟩

theorem incr_marker (c : Bool) (W : List Bool) (pos : ℕ) (hW : readTapeBit W pos = true) :
    step incrMachine (icfg (mstate c) W pos) = some (icfg (bstate c) W (pos + 1)) := by
  cases c <;> simp [step, incrMachine, icfg, Configuration.scanned, hW, mstate, bstate, carOf] <;>
    apply configuration_ext
  all_goals first
    | (funext i; simp [applyAction, HeadMove.apply])
    | rfl

theorem incr_halt (c : Bool) (W : List Bool) (pos : ℕ) (hW : readTapeBit W pos = false) :
    step incrMachine (icfg (mstate c) W pos) = some (icfg 4 W (pos + 1)) := by
  cases c <;> simp [step, incrMachine, icfg, Configuration.scanned, hW, mstate, carOf] <;>
    apply configuration_ext
  all_goals first
    | (funext i; simp [applyAction, HeadMove.apply])
    | rfl

theorem incr_bit (c b : Bool) (aW tW : List Bool)
    (hW : readTapeBit (aW ++ b :: tW) aW.length = b) :
    step incrMachine (icfg (bstate c) (aW ++ b :: tW) aW.length) =
      some (icfg (mstate (b && c)) (aW ++ xor b c :: tW) (aW.length + 1)) := by
  cases c <;>
    simp [step, incrMachine, icfg, Configuration.scanned, hW, mstate, bstate, carOf] <;>
    apply configuration_ext
  all_goals first
    | (funext i; simp [applyAction, HeadMove.apply, write_mid])
    | rfl

theorem incr_timed :
    ∀ (ws aW : List Bool) (c : Bool),
      Timed incrMachine (2 * ws.length + 1) (icfg (mstate c) (aW ++ frame ws) aW.length)
        (icfg 4 (aW ++ frame (Add.sum ws (List.replicate ws.length false) c))
          (aW.length + 2 * ws.length + 1)) := by
  intro ws
  induction ws with
  | nil =>
    intro aW c
    have hread : readTapeBit (aW ++ frame ([] : List Bool)) aW.length = false := by
      simpa [frame] using Streaming.read_append aW ([] : List Bool) false
    have h := Timed.single (p := incrMachine) (by cases c <;> rfl)
      (incr_halt c (aW ++ frame ([] : List Bool)) aW.length hread)
    simpa [frame, Add.sum] using h
  | cons b ws ih =>
    intro aW c
    have hmark : readTapeBit (aW ++ frame (b :: ws)) aW.length = true := by
      simpa [frame, List.append_assoc] using Streaming.read_append aW (b :: frame ws) true
    have hfirst := incr_marker c (aW ++ frame (b :: ws)) aW.length hmark
    have hreadb : readTapeBit ((aW ++ [true]) ++ b :: frame ws) (aW ++ [true]).length = b :=
      Streaming.read_append (aW ++ [true]) (frame ws) b
    have hsecond : step incrMachine (icfg (bstate c) (aW ++ frame (b :: ws)) (aW.length + 1)) =
        some (icfg (mstate (b && c)) ((aW ++ [true, xor b c]) ++ frame ws) (aW.length + 2)) := by
      have h := incr_bit c b (aW ++ [true]) (frame ws) hreadb
      simp only [List.length_append, List.length_cons, List.length_nil] at h
      simpa [frame, List.append_assoc] using h
    have htail := ih (aW ++ [true, xor b c]) (b && c)
    have hlen : (aW ++ [true, xor b c]).length = aW.length + 2 := by simp
    rw [hlen] at htail
    have hjoin := (Timed.single (p := incrMachine) (by cases c <;> rfl) hfirst).trans
      ((Timed.single (p := incrMachine) (by cases c <;> rfl) hsecond).trans htail)
    have htime : 1 + (1 + (2 * ws.length + 1)) = 2 * (b :: ws).length + 1 := by simp; omega
    have hpos : aW.length + 2 + 2 * ws.length + 1 = aW.length + 2 * (b :: ws).length + 1 := by
      simp; omega
    rw [htime, hpos] at hjoin
    simpa [List.replicate_succ, Add.sum, Add.bit, Add.carry, frame, List.append_assoc] using hjoin

/-- One pass increments a framed word modulo `2 ^ L`. -/
theorem incr_step (ws : List Bool) :
    Step incrMachine (2 * ws.length + 1) (fun _ => 0) (fun _ => frame ws)
      (fun _ => 2 * ws.length + 1)
      (fun _ => frame (Add.sum ws (List.replicate ws.length false) true)) := by
  have h := incr_timed ws [] true
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at h
  obtain ⟨r, hr, hf, hs⟩ := h.run (by rfl)
  refine Step.of_run (r := r) ?_ ?_ ?_
  · have hc : icfg (mstate true) (frame ws) 0 =
        (⟨incrMachine.start, (fun _ => 0), (fun _ => frame ws)⟩ : Configuration 1 5) := by
      apply configuration_ext
      · rfl
      · rfl
      · rfl
    rw [hc] at hr
    exact hr
  · rw [hf]; rfl
  · rw [hf]; rfl

theorem value_replicate_false (n : ℕ) : value (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, value, ih]

theorem incr_value (ws : List Bool) :
    value (Add.sum ws (List.replicate ws.length false) true) =
      (value ws + 1) % 2 ^ ws.length := by
  have hw : ws.length = (List.replicate ws.length false).length := by simp
  have hsum := Add.sum_value ws (List.replicate ws.length false) true hw
  have hlt : value (Add.sum ws (List.replicate ws.length false) true) < 2 ^ ws.length := by
    have h := value_lt (Add.sum ws (List.replicate ws.length false) true)
    rwa [Add.sum_length _ _ _ hw] at h
  rw [value_replicate_false ws.length] at hsum
  have hf0 : (false : Bool).toNat = 0 := rfl
  have ht1 : (true : Bool).toNat = 1 := rfl
  cases hov : Add.overflow ws (List.replicate ws.length false) true
  · rw [hov, hf0, ht1] at hsum
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [hov, ht1] at hsum
    rw [show value ws + 1 = value (Add.sum ws (List.replicate ws.length false) true) +
      2 ^ ws.length from by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]

end NearCubicWires.RepairOrdinary.FinalPrimeCursor

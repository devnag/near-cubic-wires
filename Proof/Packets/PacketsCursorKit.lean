import Proof.Packets.PacketsMetaPair

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.PacketsGlue.CursorKit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.PacketsGlue.RequestMeta
noncomputable section

/-- A framed binary word. -/
abbrev fb (w x : ℕ) : List Bool := frame (binary w x)

theorem binary_zero (width : ℕ) : binary width 0 = List.replicate width false := by
  induction width with
  | zero => rfl
  | succ width ih => simp [binary, List.replicate_succ, ih]

theorem pair_eq (a b : List Bool) :
    (Fin.addCases (motive := fun _ : Fin (1+1) => List Bool) (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)) = ![a, b] := by
  funext i
  fin_cases i <;> rfl

theorem pairH_eq :
    (Fin.addCases (motive := fun _ : Fin (1+1) => ℕ) (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)) = (fun _ => 0) := by
  funext i
  fin_cases i <;> rfl

namespace Clear

def machine : Machine 1 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q scanned =>
    if q.val = 0 then
      (if scanned 0 then some ⟨1, fun _ => none, fun _ => .right⟩
        else some ⟨2, fun _ => none, fun _ => .right⟩)
    else if q.val = 1 then some ⟨0, fun _ => some false, fun _ => .right⟩
    else none

def cfg (q : Fin 3) (W : List Bool) (pos : ℕ) : Configuration 1 3 :=
  ⟨q, fun _ => pos, fun _ => W⟩

theorem write_mid (pre tail : List Bool) (old v : Bool) :
    writeTapeBit (pre ++ old :: tail) pre.length v = pre ++ v :: tail := by
  induction pre with
  | nil => rfl
  | cons b pre ih => simpa [writeTapeBit] using congrArg (List.cons b) ih

theorem s_marker (W : List Bool) (pos : ℕ) (hW : readTapeBit W pos = true) :
    step machine (cfg 0 W pos) = some (cfg 1 W (pos + 1)) := by
  simp [step, machine, cfg, Configuration.scanned, hW]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · funext i; simp [applyAction]

theorem s_halt (W : List Bool) (pos : ℕ) (hW : readTapeBit W pos = false) :
    step machine (cfg 0 W pos) = some (cfg 2 W (pos + 1)) := by
  simp [step, machine, cfg, Configuration.scanned, hW]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · funext i; simp [applyAction]

theorem s_bit (b : Bool) (aW tW : List Bool) :
    step machine (cfg 1 (aW ++ b :: tW) aW.length) =
      some (cfg 0 (aW ++ false :: tW) (aW.length + 1)) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · funext i; simp [applyAction, write_mid]

theorem timed :
    ∀ (ws aW : List Bool),
      Timed machine (2 * ws.length + 1) (cfg 0 (aW ++ frame ws) aW.length)
        (cfg 2 (aW ++ frame (List.replicate ws.length false)) (aW.length + 2 * ws.length + 1)) := by
  intro ws
  induction ws with
  | nil =>
    intro aW
    have hread : readTapeBit (aW ++ frame ([] : List Bool)) aW.length = false := by
      simpa [frame] using Streaming.read_append aW ([] : List Bool) false
    have h := Timed.single (p := machine) (by rfl) (s_halt (aW ++ frame ([] : List Bool)) aW.length hread)
    simpa [frame] using h
  | cons b ws ih =>
    intro aW
    have hmark : readTapeBit (aW ++ frame (b :: ws)) aW.length = true := by
      simpa [frame, List.append_assoc] using Streaming.read_append aW (b :: frame ws) true
    have hfirst := s_marker (aW ++ frame (b :: ws)) aW.length hmark
    have hsecond : step machine (cfg 1 (aW ++ frame (b :: ws)) (aW.length + 1)) =
        some (cfg 0 ((aW ++ [true, false]) ++ frame ws) (aW.length + 2)) := by
      have h := s_bit b (aW ++ [true]) (frame ws)
      simp only [List.length_append, List.length_cons, List.length_nil] at h
      simpa [frame, List.append_assoc] using h
    have htail := ih (aW ++ [true, false])
    have hlen : (aW ++ [true, false]).length = aW.length + 2 := by simp
    rw [hlen] at htail
    have hjoin := (Timed.single (p := machine) (by rfl) hfirst).trans
      ((Timed.single (p := machine) (by rfl) hsecond).trans htail)
    have htime : 1 + (1 + (2 * ws.length + 1)) = 2 * (b :: ws).length + 1 := by simp; omega
    have hpos : aW.length + 2 + 2 * ws.length + 1 = aW.length + 2 * (b :: ws).length + 1 := by
      simp; omega
    rw [htime, hpos] at hjoin
    simpa [List.replicate_succ, frame, List.append_assoc] using hjoin

theorem step1 (ws : List Bool) :
    Step machine (2 * ws.length + 1) (fun _ => 0) (fun _ => frame ws) (fun _ => 2 * ws.length + 1)
      (fun _ => frame (binary ws.length 0)) := by
  have h := timed ws []
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at h
  obtain ⟨r, hr, hf, hs⟩ := h.run (by rfl)
  rw [binary_zero]
  refine Step.of_run (r := r) ?_ ?_ ?_
  · have hc : cfg 0 (frame ws) 0 =
        (⟨machine.start, (fun _ => 0), (fun _ => frame ws)⟩ : Configuration 1 3) := by
      apply configuration_ext
      · rfl
      · rfl
      · rfl
    rw [hc] at hr
    exact hr
  · rw [hf]; rfl
  · rw [hf]; rfl

end Clear

/-- **Clear, masked**: `fb w x ↦ fb w 0`, heads back at `0`, the log `0^cL` restored. -/
theorem clr_local (w x cL : ℕ) (hc : 2 * w + 1 ≤ cL) :
    Step (MaskedReset.machine Clear.machine (fun _ => true)) (2 * (2 * w + 1) + 2)
      (fun _ => 0) ![fb w x, List.replicate cL false] (fun _ => 0) ![fb w 0, List.replicate cL false] := by
  have h := (Clear.step1 (binary w x)).mask (fun _ => true) (fun _ _ => rfl) (cap := cL)
    (by rw [binary_length]; exact hc)
  rw [binary_length] at h
  have eH' : (Fin.addCases (motive := fun _ : Fin (1+1) => ℕ)
      (fun i : Fin 1 => if (fun _ => true) i = true then 0 else (fun _ => 2 * w + 1) i) (fun _ : Fin 1 => 0)) =
      (fun _ => 0) := by
    funext i; fin_cases i <;> rfl
  rw [pairH_eq, eH', pair_eq, pair_eq] at h
  exact h

/-! ## 2. The increment -/

theorem inc_local (w x cI : ℕ) (hx : x + 1 < 2 ^ w) (hc : 2 * w ≤ cI) :
    Step FramedIncrement.machine (4 * w + 2) (fun _ => 0) ![fb w x, List.replicate cI false]
      (fun _ => 0) ![fb w (x + 1), List.replicate cI false] := by
  obtain ⟨r, hr, h0, h1, hh, _, _⟩ := FramedIncrement.increment_run w x cI hx hc
  rw [← pair_eq, ← pair_eq]
  apply Step.of_run hr (funext hh)
  funext i
  fin_cases i
  · exact h0
  · exact h1

/-! ## 3. The carry flag -/

/-- The carry value: `1` iff the level overflows (`b ≤ d + 1`). -/
def carryV (b d : ℕ) : ℕ := if b ≤ d + 1 then 1 else 0

theorem carryV_le (b d : ℕ) : carryV b d ≤ 1 := by unfold carryV; split_ifs <;> omega

theorem read_tpl (d i : ℕ) : readTapeBit (UnaryTemplate.tape d) (i + 1) = decide (i < d) := by
  by_cases h : i < d
  · rw [UnaryTemplate.tape_mark d i h]; simp [h]
  · have hl : (UnaryTemplate.tape d).length = d + 2 := UnaryTemplate.tape_length d
    by_cases he : i = d
    · subst he; rw [UnaryTemplate.tape_end]; simp
    · have hi : d + 2 ≤ i + 1 := by omega
      unfold readTapeBit
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      simp [h]

namespace Carry

/-- Tapes: `0` the bound `1^b`, `1` the template of `d`, `2` the flag. -/
def machine : Machine 3 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 3
  rule := fun q c =>
    if q.val = 0 then some ⟨1, fun _ => none, ![.stay, .right, .stay]⟩
    else if q.val = 1 then
      (if c 0 && c 1 then some ⟨1, fun _ => none, ![.right, .right, .stay]⟩
       else if c 0 then some ⟨2, fun _ => none, ![.right, .stay, .stay]⟩
       else some ⟨3, ![none, none, some true], fun _ => .stay⟩)
    else if q.val = 2 then
      (if c 0 then some ⟨3, fun _ => none, fun _ => .stay⟩
       else some ⟨3, ![none, none, some true], fun _ => .stay⟩)
    else none

def cfg (q : Fin 4) (b d i j : ℕ) (o : List Bool) : Configuration 3 4 :=
  ⟨q, ![i, j, 0], ![List.replicate b true, UnaryTemplate.tape d, o]⟩

theorem s0 (b d : ℕ) : step machine (cfg 0 b d 0 0 []) = some (cfg 1 b d 0 1 []) := by
  simp only [step, machine, cfg, Configuration.scanned]
  simp
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction]

theorem s_scan (b d i : ℕ) (hb : i < b) (hd : i < d) :
    step machine (cfg 1 b d i (i + 1) []) = some (cfg 1 b d (i + 1) (i + 2) []) := by
  have h0 := read_rep b i
  have h1 := read_tpl d i
  simp only [step, machine, cfg, Configuration.scanned]
  simp [h0, h1, hb, hd]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction]

theorem s_low (b d : ℕ) (hb : b ≤ d) :
    step machine (cfg 1 b d b (b + 1) []) = some (cfg 3 b d b (b + 1) [true]) := by
  have h0 := read_rep b b
  simp only [step, machine, cfg, Configuration.scanned]
  simp [h0]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, writeTapeBit]

theorem s_hit (b d : ℕ) (hb : d < b) :
    step machine (cfg 1 b d d (d + 1) []) = some (cfg 2 b d (d + 1) (d + 1) []) := by
  have h0 := read_rep b d
  have h1 := read_tpl d d
  simp only [step, machine, cfg, Configuration.scanned]
  simp [h0, h1, hb]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction]

theorem s_far (b d : ℕ) (hb : d + 1 < b) :
    step machine (cfg 2 b d (d + 1) (d + 1) []) = some (cfg 3 b d (d + 1) (d + 1) []) := by
  have h0 := read_rep b (d + 1)
  simp only [step, machine, cfg, Configuration.scanned]
  simp [h0, hb]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction]

theorem s_edge (b d : ℕ) (hb : b = d + 1) :
    step machine (cfg 2 b d (d + 1) (d + 1) []) = some (cfg 3 b d (d + 1) (d + 1) [true]) := by
  subst hb
  have h0 := read_rep (d + 1) (d + 1)
  simp only [step, machine, cfg, Configuration.scanned]
  simp [h0]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, writeTapeBit]

theorem scan (b d : ℕ) : ∀ n i, i + n ≤ b → i + n ≤ d →
    Timed machine n (cfg 1 b d i (i + 1) []) (cfg 1 b d (i + n) (i + n + 1) []) := by
  intro n
  induction n with
  | zero => intro i _ _; exact Timed.refl _ _
  | succ n ih =>
    intro i hb hd
    have t1 := Timed.single (p := machine) (by simp [machine, cfg]) (s_scan b d i (by omega) (by omega))
    have t2 := ih (i + 1) (by omega) (by omega)
    have t := t1.trans t2
    rw [show i + 1 + n = i + (n + 1) by omega, show 1 + n = n + 1 by omega] at t
    exact t

/-- The raw run: the flag written, heads anywhere. -/
theorem run (b d : ℕ) : ∃ (n : ℕ) (H : Fin 3 → ℕ), n ≤ b + 3 ∧
    Step machine n ![0, 0, 0] ![List.replicate b true, UnaryTemplate.tape d, []] H
      ![List.replicate b true, UnaryTemplate.tape d, List.replicate (carryV b d) true] := by
  have e0 : (⟨machine.start, ![0, 0, 0], ![List.replicate b true, UnaryTemplate.tape d, []]⟩ :
      Configuration 3 4) = cfg 0 b d 0 0 [] := rfl
  have t0 := Timed.single (p := machine) (by simp [machine, cfg]) (s0 b d)
  by_cases hbd : b ≤ d
  · have ts := scan b d b 0 (by omega) (by omega)
    simp only [Nat.zero_add] at ts
    have t3 := Timed.single (p := machine) (by simp [machine, cfg]) (s_low b d hbd)
    obtain ⟨r, hr, hf, hs⟩ := (t0.trans (ts.trans t3)).run (by simp [machine, cfg])
    refine ⟨1 + (b + 1), _, by omega, r, ?_, rfl, ?_, by omega⟩
    · rw [e0]; exact hr
    · rw [hf]; simp only [cfg, carryV, if_pos (by omega : b ≤ d + 1)]; rfl
  · have ts := scan b d d 0 (by omega) (by omega)
    simp only [Nat.zero_add] at ts
    have t3 := Timed.single (p := machine) (by simp [machine, cfg]) (s_hit b d (by omega))
    by_cases hfar : d + 1 < b
    · have t4 := Timed.single (p := machine) (by simp [machine, cfg]) (s_far b d hfar)
      obtain ⟨r, hr, hf, hs⟩ := (t0.trans (ts.trans (t3.trans t4))).run (by simp [machine, cfg])
      refine ⟨1 + (d + (1 + 1)), _, by omega, r, ?_, rfl, ?_, by omega⟩
      · rw [e0]; exact hr
      · rw [hf]; simp only [cfg, carryV, if_neg (by omega : ¬ b ≤ d + 1)]; rfl
    · have t4 := Timed.single (p := machine) (by simp [machine, cfg]) (s_edge b d (by omega))
      obtain ⟨r, hr, hf, hs⟩ := (t0.trans (ts.trans (t3.trans t4))).run (by simp [machine, cfg])
      refine ⟨1 + (d + (1 + 1)), _, by omega, r, ?_, rfl, ?_, by omega⟩
      · rw [e0]; exact hr
      · rw [hf]; simp only [cfg, carryV, if_pos (by omega : b ≤ d + 1)]; rfl

end Carry

/-- **The carry flag, masked** (log from empty): `[b ≤ d + 1]` on tape 2, every head back at `0`. -/
theorem carry_local (b d : ℕ) : ∃ k, Step (MaskedReset.machine Carry.machine (fun _ => true)) (2 * (b + 3) + 2)
    (fun _ => 0) ![List.replicate b true, UnaryTemplate.tape d, [], []]
    (fun _ => 0) ![List.replicate b true, UnaryTemplate.tape d, List.replicate (carryV b d) true,
      List.replicate k false] := by
  obtain ⟨n, H, hn, hs⟩ := Carry.run b d
  obtain ⟨k, hm⟩ := step_mask0 (hs.enlarge hn) (fun _ => true) (by intro i _; fin_cases i <;> rfl)
  refine ⟨k, hm.congr_in ?_ ?_ |>.congr ?_ ?_⟩
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-! ## 4. The unary template to `1^d` -/

namespace TplU

end TplU

/-! ## 6. Erasing cell 0 of eight tapes in one step -/

namespace Zap

end Zap

/-! ## 7. The erase driver's own erase: `1^E ↦ 0^E` -/

namespace DErase

def machine : Machine 1 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q c =>
    if q.val = 0 then
      (if c 0 then some ⟨0, fun _ => none, fun _ => .right⟩ else some ⟨1, fun _ => none, fun _ => .left⟩)
    else if q.val = 1 then
      (if c 0 then some ⟨1, fun _ => some false, fun _ => .left⟩ else some ⟨2, fun _ => none, fun _ => .stay⟩)
    else none

def cfg (q : Fin 3) (T : List Bool) (p : ℕ) : Configuration 1 3 := ⟨q, fun _ => p, fun _ => T⟩

theorem s_right (E p : ℕ) (hp : p < E) :
    step machine (cfg 0 (List.replicate E true) p) = some (cfg 0 (List.replicate E true) (p + 1)) := by
  have h := read_rep E p
  simp [step, machine, cfg, Configuration.scanned, h, hp]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · funext i; simp [applyAction]

theorem s_turn (E : ℕ) :
    step machine (cfg 0 (List.replicate E true) E) = some (cfg 1 (List.replicate E true) (E - 1)) := by
  have h := read_rep E E
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · funext i; simp [applyAction]

def half (E p : ℕ) : List Bool := List.replicate (p + 1) true ++ List.replicate (E - (p + 1)) false

theorem write_half (E p : ℕ) (hp : p + 1 ≤ E) :
    writeTapeBit (half E p) p false = List.replicate p true ++ List.replicate (E - p) false := by
  unfold half
  have e1 : List.replicate (p + 1) true = List.replicate p true ++ [true] := by
    rw [List.replicate_succ']
  rw [e1, List.append_assoc]
  have hw := Clear.write_mid (List.replicate p true) (List.replicate (E - (p + 1)) false) true false
  simp only [List.length_replicate] at hw
  simp only [List.singleton_append]
  rw [hw]
  congr 1
  rw [show E - p = (E - (p + 1)) + 1 by omega, List.replicate_succ]

theorem read_half (E p : ℕ) (hp : p + 1 ≤ E) : readTapeBit (half E p) p = true := by
  unfold half readTapeBit
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp)]
  simp

theorem s_erase (E p : ℕ) (hp : p + 1 ≤ E) :
    step machine (cfg 1 (half E p) p) =
      some (cfg 1 (List.replicate p true ++ List.replicate (E - p) false) (p - 1)) := by
  have h := read_half E p hp
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · funext i; simp [applyAction, write_half E p hp]

theorem right_scan (E : ℕ) : ∀ n p, p + n ≤ E →
    Timed machine n (cfg 0 (List.replicate E true) p) (cfg 0 (List.replicate E true) (p + n)) := by
  intro n
  induction n with
  | zero => intro p _; exact Timed.refl _ _
  | succ n ih =>
    intro p hp
    have t1 := Timed.single (p := machine) (by simp [machine, cfg]) (s_right E p (by omega))
    have t2 := ih (p + 1) (by omega)
    have t := t1.trans t2
    rw [show p + 1 + n = p + (n + 1) by omega, show 1 + n = n + 1 by omega] at t
    exact t

/-- From head `p` (cells `0..p` still ones), erase leftwards down to cell `0`. -/
theorem left_erase (E : ℕ) : ∀ p, p + 1 ≤ E →
    Timed machine (p + 1) (cfg 1 (half E p) p) (cfg 1 (List.replicate E false) 0) := by
  intro p
  induction p with
  | zero =>
    intro hE
    have t := Timed.single (p := machine) (by simp [machine, cfg]) (s_erase E 0 hE)
    simpa using t
  | succ p ih =>
    intro hE
    have t1 := Timed.single (p := machine) (by simp [machine, cfg]) (s_erase E (p + 1) hE)
    have e : List.replicate (p + 1) true ++ List.replicate (E - (p + 1)) false = half E p := rfl
    simp only [Nat.add_sub_cancel] at t1
    rw [e] at t1
    have t := t1.trans (ih (by omega))
    rw [show 1 + (p + 1) = p + 1 + 1 by omega] at t
    exact t

theorem s_stop (E : ℕ) : step machine (cfg 1 (List.replicate E false) 0) = some (cfg 2 (List.replicate E false) 0) := by
  have h : readTapeBit (List.replicate E false) 0 = false := by
    unfold readTapeBit; rw [List.getD_eq_getElem?_getD]; cases E <;> simp
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · funext i; simp [applyAction]

theorem run (E : ℕ) :
    Step machine (2 * E + 2) (fun _ => 0) (fun _ => List.replicate E true) (fun _ => 0)
      (fun _ => List.replicate E false) := by
  have e0 : (⟨machine.start, fun _ => 0, fun _ => List.replicate E true⟩ : Configuration 1 3) =
      cfg 0 (List.replicate E true) 0 := rfl
  have t1 := right_scan E E 0 (by omega)
  simp only [Nat.zero_add] at t1
  have t2 := Timed.single (p := machine) (by simp [machine, cfg]) (s_turn E)
  rcases Nat.eq_zero_or_pos E with hE | hE
  · subst hE
    have t3 := Timed.single (p := machine) (by simp [machine, cfg]) (s_stop 0)
    have t := t1.trans (t2.trans t3)
    obtain ⟨r, hr, hf, hs⟩ := t.run (by simp [machine, cfg])
    refine Step.enlarge (n := 0 + (1 + 1)) ?_ (by omega)
    exact Step.of_run (by rw [e0]; exact hr) (by rw [hf]; rfl) (by rw [hf]; rfl)
  · have eh : half E (E - 1) = List.replicate E true := by
      unfold half; rw [show E - 1 + 1 = E by omega, Nat.sub_self]; simp
    have t3 := left_erase E (E - 1) (by omega)
    rw [eh] at t3
    have t4 := Timed.single (p := machine) (by simp [machine, cfg]) (s_stop E)
    have t := t1.trans (t2.trans (t3.trans t4))
    obtain ⟨r, hr, hf, hs⟩ := t.run (by simp [machine, cfg])
    refine Step.enlarge (n := E + (1 + (E - 1 + 1 + 1))) ?_ (by omega)
    exact Step.of_run (by rw [e0]; exact hr) (by rw [hf]; rfl) (by rw [hf]; rfl)

end DErase

end
end NearCubicWires.PacketsGlue.CursorKit


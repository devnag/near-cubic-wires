import Proof.Packets.PacketsMetaSeedCount
import Proof.Packets.PacketsKeysScan
import Proof.Packets.PacketsDock

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsMeta.KeyDecode
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsMeta NearCubicWires.PacketsGlue.RequestMeta
noncomputable section

/-! ## 1. One left move -/

def moveL : Machine 1 2 := oneStep 1 (fun _ => (fun _ => none, fun _ => .left))

theorem moveL_lruns (W h : ℕ) (f : ℕ → Bool) : LRuns W moveL 1 ![.cells f (h + 1)] ![.cells f h] := by
  intro H A hA
  have h0 : H 0 = h + 1 ∧ ∀ j, readTapeBit (A 0) j = f j := hA 0
  refine ⟨_, _, oneStep_run 1 _ H A, ?_⟩
  intro i
  fin_cases i
  exact ⟨by simp [HeadMove.apply, h0.1], h0.2⟩

/-! ## 2. The exact frame copier -/

namespace FC

/-- Tape 0 the framed word (read only), tape 1 the copy. State 0 at a marker cell (copy it; a `false`
marker ends the frame: copy it and halt), state 1 at a payload cell (copy it). -/
def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q b =>
    if q.val = 0 then some (if b 0 then ⟨1, ![none, some true], ![.right, .right]⟩
      else ⟨2, ![none, some false], ![.stay, .stay]⟩)
    else if q.val = 1 then some ⟨0, ![none, some (b 0)], ![.right, .right]⟩
    else none

def cfg (F : List Bool) (q : Fin 3) (p : ℕ) : Configuration 2 3 := ⟨q, ![p, p], ![F, F.take p]⟩

theorem write_take (F : List Bool) (p : ℕ) (hp : p < F.length) (b : Bool) (hb : readTapeBit F p = b) :
    writeTapeBit (F.take p) p b = F.take (p + 1) := by
  have hl : (F.take p).length = p := by simp; omega
  have hw := Streaming.write_append (F.take p) b
  rw [hl] at hw
  have hr : b = F[p] := by rw [← hb]; unfold readTapeBit; rw [List.getD_eq_getElem _ _ hp]
  rw [hw, List.take_add_one, List.getElem?_eq_getElem hp, hr]
  rfl

theorem sMark (F : List Bool) (p : ℕ) (hp : p < F.length) (hr : readTapeBit F p = true) :
    step machine (cfg F 0 p) = some (cfg F 1 (p + 1)) := by
  have hw := write_take F p hp true hr
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, hw]

theorem sBit (F : List Bool) (p : ℕ) (hp : p < F.length) :
    step machine (cfg F 1 p) = some (cfg F 0 (p + 1)) := by
  have hw := write_take F p hp (readTapeBit F p) rfl
  simp [step, machine, cfg, Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, hw]

theorem sEnd (F : List Bool) (p : ℕ) (hp : p < F.length) (hr : readTapeBit F p = false) :
    step machine (cfg F 0 p) = some ⟨2, ![p, p], ![F, F.take (p + 1)]⟩ := by
  have hw := write_take F p hp false hr
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, hw]

theorem loop (w : List Bool) : ∀ i, i ≤ w.length →
    Timed machine (2 * i) (cfg (frame w) 0 0) (cfg (frame w) 0 (2 * i)) := by
  intro i
  induction i with
  | zero => intro _; exact Timed.refl _ _
  | succ i ih =>
    intro hi
    have hlen := frame_length w
    have t1 := ih (by omega)
    have t2 := Timed.single (p := machine) (by rfl)
      (sMark (frame w) (2 * i) (by omega) (NearCubicWires.PacketsGlue.NatSum.read_marker w i (by omega)))
    have t3 := Timed.single (p := machine) (by rfl) (sBit (frame w) (2 * i + 1) (by omega))
    have t := (t1.trans t2).trans t3
    rw [show 2 * i + 1 + 1 = 2 * (i + 1) by omega] at t
    exact t

/-- **The copy**: both tapes end holding `frame w`, heads at `2|w|`. -/
theorem run (w : List Bool) :
    Step machine (2 * w.length + 1) ![0, 0] ![frame w, []] ![2 * w.length, 2 * w.length] ![frame w, frame w] := by
  have hlen := frame_length w
  have t1 := loop w w.length le_rfl
  have t2 := Timed.single (p := machine) (by rfl)
    (sEnd (frame w) (2 * w.length) (by omega) (NearCubicWires.PacketsGlue.NatSum.read_end w))
  have t := t1.trans t2
  obtain ⟨r, hr, hf, _⟩ := t.run (by rfl)
  have htake : (frame w).take (2 * w.length + 1) = frame w := by
    rw [List.take_of_length_le (by omega)]
  refine Step.of_run (r := r) ?_ (by rw [hf]) (by rw [hf, htake])
  have hc : cfg (frame w) 0 0 = (⟨machine.start, ![0, 0], ![frame w, []]⟩ : Configuration 2 3) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [← hc]
  exact hr

end FC

/-- The copier under a masked reset of both heads (one log tape). -/
def fcM := MaskedReset.machine FC.machine (fun _ => true)

theorem fc_run (w : List Bool) : ∃ k, Step fcM (2 * (2 * w.length + 1) + 2) (fun _ => 0) ![frame w, [], []]
    (fun _ => 0) ![frame w, frame w, List.replicate k false] := by
  obtain ⟨k, hm⟩ := step_mask0 (FC.run w) (fun _ => true) (by intro i _; fin_cases i <;> rfl)
  refine ⟨k, (hm.congr_in ?_ ?_).congr ?_ ?_⟩
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-! ## 3. On the copy: unframe, one left move, the output loop -/

theorem binary_getD : ∀ (W d i : ℕ), i < W → (SignedSortKey.binary W d).getD i false = d.testBit i
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | W + 1, d, 0, _ => by
    rcases Nat.mod_two_eq_zero_or_one d with h | h <;> simp [SignedSortKey.binary, Nat.testBit_zero, h]
  | W + 1, d, i + 1, h => by
    simp only [SignedSortKey.binary, List.getD_cons_succ]
    rw [binary_getD W (d / 2) i (by omega), Nat.testBit_succ]

theorem sf_binary (W d j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ W) :
    sf (SignedSortKey.binary W d) j = d.testBit (j - 1) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [sf_succ, binary_getD W d i (by omega)]
  rfl

def decP :=
  Composition.machine (RecoveryFocus.machine ![(0 : Fin 7), 1, 2, 3] (PacketsKeys.Setup.machine 1))
    (Composition.machine (RecoveryFocus.machine ![(1 : Fin 7)] moveL)
      (RecoveryFocus.machine ![(3 : Fin 7), 4, 1, 5, 6] PacketsKeys.Emit.machine))

section Roles
variable (w : List Bool)

def r0 : Fin 7 → TS := ![.cells (PacketsKeys.Setup.ff w) 0, .cells blank 0, .cells blank 0, .cells blank 0,
  .cells blank 0, .cells blank 0, .out 0]
def r1 : Fin 7 → TS := ![.cells (PacketsKeys.Setup.ff w) (frame w).length, .cells (sf w) 1,
  .cells (PacketsKeys.Setup.mk w) 1, .ruler, .cells blank 0, .cells blank 0, .out 0]
def r2 : Fin 7 → TS := ![.cells (PacketsKeys.Setup.ff w) (frame w).length, .cells (sf w) 0,
  .cells (PacketsKeys.Setup.mk w) 1, .ruler, .cells blank 0, .cells blank 0, .out 0]
def r3 (d : ℕ) : Fin 7 → TS := ![.cells (PacketsKeys.Setup.ff w) (frame w).length, .reg d,
  .cells (PacketsKeys.Setup.mk w) 1, .ruler, .reg 0, .flag false, .out 0]
def r4 (d : ℕ) : Fin 7 → TS := ![.cells (PacketsKeys.Setup.ff w) (frame w).length, .reg 0,
  .cells (PacketsKeys.Setup.mk w) 1, .ruler, .reg 0, .flag false, .out (0 + d)]

end Roles

/-- The loop fuel of the decode at width `W` and value `V`. -/
def emitCost (W V : ℕ) : ℕ := (V + 1) * ((2 * W + 3) + (2 * W + 3 + 1 + 1) + 2)

def pCost (W V : ℕ) : ℕ := PacketsKeys.Setup.cost 1 W + 1 + (1 + 1 + emitCost (1 * W) V)

theorem decP_lruns (W d : ℕ) (hd : d < 2 ^ W) :
    LRuns (1 * (SignedSortKey.binary W d).length) decP (pCost W d)
      (r0 (SignedSortKey.binary W d)) (r4 (SignedSortKey.binary W d) d) := by
  set w := SignedSortKey.binary W d with hwdef
  have hwl : w.length = W := by rw [hwdef, SignedSortKey.binary_length]
  have h1 : LRuns (1 * w.length) (RecoveryFocus.machine ![(0 : Fin 7), 1, 2, 3] (PacketsKeys.Setup.machine 1))
      (PacketsKeys.Setup.cost 1 w.length) (r0 w) (r1 w) :=
    ((PacketsKeys.Setup.run 1 le_rfl w).dockK ![(0 : Fin 7), 1, 2, 3] (by decide) (r0 w)
      (by intro j; fin_cases j <;> rfl) [0, 1, 2, 3]
      (by intro j hj; fin_cases j <;> simp at hj)).congr_out (by funext j; fin_cases j <;> rfl)
  have h2 : LRuns (1 * w.length) (RecoveryFocus.machine ![(1 : Fin 7)] moveL) 1 (r1 w) (r2 w) :=
    ((moveL_lruns (1 * w.length) 0 (sf w)).dockK ![(1 : Fin 7)] (by decide) (r1 w)
      (by intro j; fin_cases j; rfl) [0] (by intro j hj; fin_cases j; simp at hj)).congr_out
      (by funext j; fin_cases j <;> rfl)
  have h2w : LRuns (1 * w.length) (RecoveryFocus.machine ![(1 : Fin 7)] moveL) 1 (r1 w) (r3 w d) := by
    refine h2.weaken ?_
    intro i H A hA
    fin_cases i
    · exact hA
    · obtain ⟨hH, hR⟩ := hA
      refine ⟨hH, fun j hj1 hj2 => ?_⟩
      rw [hR j]
      exact sf_binary W d j hj1 (by rw [hwl] at hj2; omega)
    · exact hA
    · exact hA
    · obtain ⟨hH, hR⟩ := hA
      refine ⟨hH, fun j _ _ => ?_⟩
      rw [hR j]
      simp [blank]
    · obtain ⟨hH, hR⟩ := hA
      exact ⟨hH, by rw [hR 0]; rfl⟩
    · exact hA
  have hd' : d < 2 ^ (1 * w.length) := by rw [hwl, Nat.one_mul]; exact hd
  have h3 : LRuns (1 * w.length) (RecoveryFocus.machine ![(3 : Fin 7), 4, 1, 5, 6] PacketsKeys.Emit.machine)
      (emitCost (1 * w.length) d) (r3 w d) (r4 w d) :=
    ((PacketsKeys.Emit.run (1 * w.length) d 0 false hd').dockK ![(3 : Fin 7), 4, 1, 5, 6] (by decide) (r3 w d)
      (by intro j; fin_cases j <;> rfl) [2, 4]
      (by intro j hj; fin_cases j <;> simp at hj ⊢)).congr_out (by funext j; fin_cases j <;> rfl)
  have h := h1.seq (h2w.seq h3)
  have e : PacketsKeys.Setup.cost 1 w.length + 1 + (1 + 1 + emitCost (1 * w.length) d) = pCost W d := by
    rw [hwl]; rfl
  exact h.enlarge (le_of_eq e)

/-- The decode from the concrete copy bank: the output tape holds exactly `1^d`. -/
theorem decP_run (W d : ℕ) (hd : d < 2 ^ W) :
    ∃ (H' : Fin 7 → ℕ) (A' : Fin 7 → List Bool),
      Step decP (pCost W d) (fun _ => 0) ![frame (SignedSortKey.binary W d), [], [], [], [], [], []] H' A' ∧
      A' 6 = List.replicate d true := by
  obtain ⟨H', A', hs, hr⟩ := decP_lruns W d hd (fun _ => 0)
    ![frame (SignedSortKey.binary W d), [], [], [], [], [], []] (by
      intro i
      fin_cases i
      · exact ⟨rfl, fun j => rfl⟩
      · exact ⟨rfl, fun j => by simp [readTapeBit, blank]⟩
      · exact ⟨rfl, fun j => by simp [readTapeBit, blank]⟩
      · exact ⟨rfl, fun j => by simp [readTapeBit, blank]⟩
      · exact ⟨rfl, fun j => by simp [readTapeBit, blank]⟩
      · exact ⟨rfl, fun j => by simp [readTapeBit, blank]⟩
      · exact ⟨rfl, rfl⟩)
  have h6 : H' 6 = 0 + d ∧ A' 6 = List.replicate (0 + d) true := hr 6
  refine ⟨H', A', hs, ?_⟩
  rw [h6.2, Nat.zero_add]

/-! ## 4. The decoder: copy, decode the copy, reset every head -/

def s1 : Fin 3 → Fin 9 := ![0, 2, 8]
def s2 : Fin 7 → Fin 9 := ![2, 3, 4, 5, 6, 7, 1]

theorem s1_inj : Function.Injective s1 := by decide
theorem s2_inj : Function.Injective s2 := by decide

def decBase := Composition.machine (RecoveryFocus.machine s1 fcM) (RecoveryFocus.machine s2 decP)

/-- **The digit decoder** (one fixed machine, 10 tapes). -/
def decM := MaskedReset.machine decBase (fun _ => true)

/-- Its entry bank: the framed field on tape 0, all else empty. -/
def decIn (F : List Bool) : Fin (9 + 1) → List Bool := fun i => if i.val = 0 then F else []

def bank0 (F : List Bool) : Fin 9 → List Bool := fun i => if i.val = 0 then F else []

/-- Its fuel at field width `W` and digit bound `B`. -/
def decCost (W B : ℕ) : ℕ := 2 * (2 * (2 * W + 1) + 2 + 1 + pCost W B) + 2

theorem pCost_mono (W d B : ℕ) (h : d ≤ B) : pCost W d ≤ pCost W B := by
  unfold pCost emitCost
  have h' : (d + 1) * ((2 * (1 * W) + 3) + (2 * (1 * W) + 3 + 1 + 1) + 2) ≤
      (B + 1) * ((2 * (1 * W) + 3) + (2 * (1 * W) + 3 + 1 + 1) + 2) := Nat.mul_le_mul_right _ (by omega)
  omega

/-- **The decoder's run.** From `frame (binary W d)` on tape 0 (all else empty, heads 0) it returns tape 0
exactly and writes `1^d` on tape 1, both heads 0, within `decCost W B` steps for any bound `B ≥ d`. -/
theorem dec_run (W d B : ℕ) (hd : d < 2 ^ W) (hdB : d ≤ B) :
    ∃ (H' : Fin (9 + 1) → ℕ) (A' : Fin (9 + 1) → List Bool),
      Step decM (decCost W B) (fun _ => 0) (decIn (frame (SignedSortKey.binary W d))) H' A' ∧
      A' ⟨0, by omega⟩ = frame (SignedSortKey.binary W d) ∧ H' ⟨0, by omega⟩ = 0 ∧
      A' ⟨1, by omega⟩ = List.replicate d true ∧ H' ⟨1, by omega⟩ = 0 := by
  set F := frame (SignedSortKey.binary W d) with hF
  have hwl : (SignedSortKey.binary W d).length = W := SignedSortKey.binary_length W d
  -- the copy
  obtain ⟨k, hfc⟩ := fc_run (SignedSortKey.binary W d)
  rw [hwl, ← hF] at hfc
  obtain ⟨H1, A1, st1, hs1, ho1⟩ := NearCubicWires.PacketsConstruction.Dock.lift hfc s1 s1_inj (fun _ => 0) (fun _ => 0) (bank0 F) (by
    intro j
    fin_cases j <;> exact ⟨rfl, by simp [bank0, s1, ZeroPadding.pad_zero]⟩)
  -- the decode on the copy
  obtain ⟨H2, A2, st2, h26⟩ := decP_run W d hd
  rw [← hF] at st2
  have hA1 : ∀ i : Fin 9, i ≠ 0 → i ≠ 2 → i ≠ 8 → H1 i = 0 ∧ A1 i = [] := by
    intro i h0 h2 h8
    have hn : ∀ j, s1 j ≠ i := by
      intro j hj; fin_cases j <;> simp [s1] at hj <;> [exact h0 hj.symm; exact h2 hj.symm; exact h8 hj.symm]
    obtain ⟨e1, e2⟩ := ho1 i hn
    refine ⟨e1, ?_⟩
    rw [e2]
    simp only [bank0]
    rw [if_neg (show ¬ (i.val = 0) from fun h => h0 (Fin.ext h))]
  obtain ⟨H3, A3, st3, hs3, ho3⟩ := NearCubicWires.PacketsConstruction.Dock.lift st2 s2 s2_inj (fun _ => 0) H1 A1 (by
    intro j
    fin_cases j
    · have h := hs1 1
      simp only [s1, ZeroPadding.pad_zero] at h
      exact ⟨h.1, by simp only [ZeroPadding.pad_zero]; exact h.2⟩
    all_goals
      first
      | exact ⟨(hA1 _ (by decide) (by decide) (by decide)).1,
          by rw [ZeroPadding.pad_zero]; exact (hA1 _ (by decide) (by decide) (by decide)).2⟩)
  have st := st1.seq st3
  obtain ⟨k', hm⟩ := step_mask0 st (fun _ => true) (by intro i _; rfl)
  have hin : (Fin.addCases (fun _ : Fin 9 => 0) (fun _ : Fin 1 => 0) : Fin (9 + 1) → ℕ) = fun _ => 0 := by
    funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  have tin : (Fin.addCases (bank0 F) (fun _ : Fin 1 => ([] : List Bool)) : Fin (9 + 1) → List Bool) = decIn F := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [bank0, decIn]
    · simp [decIn]
  have hm' := (hm.congr_in hin tin).enlarge (show 2 * (2 * (2 * W + 1) + 2 + 1 + pCost W d) + 2 ≤ decCost W B by
    unfold decCost; have := pCost_mono W d B hdB; omega)
  refine ⟨_, _, hm', ?_, ?_, ?_, ?_⟩
  · have hc : (⟨0, by omega⟩ : Fin (9 + 1)) = Fin.castAdd 1 (0 : Fin 9) := rfl
    rw [hc, Fin.addCases_left]
    have h0 : ∀ j, s2 j ≠ (0 : Fin 9) := by intro j; fin_cases j <;> decide
    rw [(ho3 0 h0).2]
    have h := hs1 0
    simp only [s1, ZeroPadding.pad_zero] at h
    exact h.2
  · have hc : (⟨0, by omega⟩ : Fin (9 + 1)) = Fin.castAdd 1 (0 : Fin 9) := rfl
    rw [hc, Fin.addCases_left]
    rfl
  · have hc : (⟨1, by omega⟩ : Fin (9 + 1)) = Fin.castAdd 1 (1 : Fin 9) := rfl
    rw [hc, Fin.addCases_left]
    have h := hs3 6
    have e6 : s2 6 = 1 := rfl
    rw [e6, ZeroPadding.pad_zero] at h
    rw [h.2, h26]
  · have hc : (⟨1, by omega⟩ : Fin (9 + 1)) = Fin.castAdd 1 (1 : Fin 9) := rfl
    rw [hc, Fin.addCases_left]
    rfl

end
end NearCubicWires.PacketsMeta.KeyDecode


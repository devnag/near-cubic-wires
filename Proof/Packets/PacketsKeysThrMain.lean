import Proof.Packets.PacketsKeysThrPro

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.PacketsKeys.ThrProg
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.PacketsMeta NearCubicWires.PacketsKeys.RM
open NearCubicWires.RepairRepresentation NearCubicWires.PacketsSymBits NearCubicWires.ThresholdAlignedEnvelope
noncomputable section

/-- The blank role. -/
abbrev bl : TS := .cells blank 0

/-- The program's entry state. -/
def zIn (tw : List Bool) (p : ℕ) (sel : Fin 4 → ℕ) (j : ℕ) : TZ where
  rl := bl
  fl := false
  P := 0
  A := 0
  K := 0
  I := 0
  X := 0
  B := 0
  Bm := 0
  F := 0
  R := 0
  M := 0
  T := 0
  MSK := 0
  MT := 0
  MM := 0
  E := 0
  Ep := 0
  E2m := 0
  Em := 0
  Jc := 0
  SG := 0
  S := fun _ => 0
  ts := bl
  tm := bl
  os := bl
  om := bl
  js := .cells (sf (List.replicate (j + 1) true)) 1
  jd := bl
  tf := .cells (PacketsKeys.Setup.ff tw) 0
  up1 := .cells (PacketsKeys.Pow.u p) 0
  d1 := bl
  up1' := .cells (PacketsKeys.Pow.u p) 0
  d1' := bl
  up2 := .cells (PacketsKeys.Pow.u p) 0
  d2 := bl
  us := fun c => .cells (PacketsKeys.Pow.u (sel c)) 0
  ds := fun _ => bl
  cc := fun _ => bl

/-- The prologue. -/
def thrPro :=
  Composition.machine (mInitOut (NR := 24) (NO := 29) oOS oOM) (Composition.machine (mUnf (NR := 24) (NO := 29) oTF oTS oTM)
  (Composition.machine (mRuleR (NR := 24) (NO := 29)) (Composition.machine (mAppendR (NR := 24) (NO := 29) 8 oTM oTS)
  (Composition.machine (extR (NR := 24) (NO := 29) oD1 oUP1) (Composition.machine (extR (NR := 24) (NO := 29) oD1' oUP1')
  (Composition.machine (mFinishR (NR := 24) (NO := 29)) (Composition.machine (loadU (NO := 29) rP oD2 oUP2)
  (Composition.machine (loadU (NO := 29) (rS 0) (oDS 0) (oUS 0)) (Composition.machine (loadU (NO := 29) (rS 1) (oDS 1) (oUS 1))
  (Composition.machine (loadU (NO := 29) (rS 2) (oDS 2) (oUS 2)) (Composition.machine (loadU (NO := 29) (rS 3) (oDS 3) (oUS 3))
  (Composition.machine (mMoveR (NR := 24) (NO := 29) oJD) (Composition.machine (loadU (NO := 29) rJc oJD oJS)
  (Composition.machine (pow2 (NO := 29) rJc rE rEp) (Composition.machine (mCpy (NO := 29) rE2m rE)
  (Composition.machine (mDec (NO := 29) rE2m) (Composition.machine (mCpy (NO := 29) rEm rEp)
  (Composition.machine (mDec (NO := 29) rEm) (mInc (NO := 29) rB)))))))))))))))))))

/-! ## The prologue's states -/

section ProStates
variable (tw : List Bool) (p : ℕ) (sel : Fin 4 → ℕ) (j : ℕ)

def pr1 : TZ := { zIn tw p sel j with os := sS [], om := sM [] }
def pr2 : TZ := { pr1 tw p sel j with tf := .cells (PacketsKeys.Setup.ff tw) (0 + (RepairOrdinary.frame tw).length), ts := .cells (sf tw) 1, tm := .cells (sf (List.replicate tw.length true)) 1 }
def pr3 : TZ := { pr2 tw p sel j with rl := .cells (Ruler.rb 1) 1 }
def pr4 : TZ := { pr3 tw p sel j with rl := .cells (Ruler.rb (1 + 8 * tw.length)) (1 + 8 * tw.length) }
def pr5 : TZ := { pr4 tw p sel j with rl := .cells (Ruler.rb (1 + 8 * tw.length + p)) (1 + 8 * tw.length + p), d1 := .cells blank (p + 1), up1 := .cells (PacketsKeys.Pow.u p) (p + 1), fl := false }
def pr6 : TZ := { pr5 tw p sel j with rl := .cells (Ruler.rb (8 * tw.length + p + p + 1)) (8 * tw.length + p + p + 1), d1' := .cells blank (p + 1), up1' := .cells (PacketsKeys.Pow.u p) (p + 1), fl := false }
def pr7 : TZ := { pr6 tw p sel j with rl := .ruler }
def pr8 : TZ := { pr7 tw p sel j with P := p, d2 := .cells blank (p + 1), up2 := .cells (PacketsKeys.Pow.u p) (p + 1), fl := false }
def prS (k : ℕ) : TZ := { pr8 tw p sel j with S := fun c => if c.val < k then sel c else 0, ds := fun c => if c.val < k then .cells blank (sel c + 1) else bl, us := fun c => if c.val < k then .cells (PacketsKeys.Pow.u (sel c)) (sel c + 1) else .cells (PacketsKeys.Pow.u (sel c)) 0 }
def pr13 : TZ := { prS tw p sel j 4 with jd := .cells blank 1 }
def pr14 : TZ := { pr13 tw p sel j with Jc := j + 1, jd := .cells blank (1 + (j + 1) + 1), js := .cells (sf (List.replicate (j + 1) true)) (1 + (j + 1) + 1), fl := false }
def pr15 : TZ := { pr14 tw p sel j with Jc := 0, E := 2 ^ (j + 1), Ep := 2 ^ (j + 1) / 2, fl := false }
def pr19 : TZ := { pr15 tw p sel j with E2m := 2 ^ (j + 1) - 1, Em := 2 ^ (j + 1) / 2 - 1, fl := false }
/-- The state after the prologue. -/
def zPro : TZ := { pr19 tw p sel j with B := 1, fl := false }

end ProStates

def proCost (W n p j : ℕ) (sel : Fin 4 → ℕ) : ℕ :=
  1 + 1 + ((5 * n + 10) + 1 + (1 + 1 + (((8 + 1) * n + n + 7) + 1 + (extCost p + 1 + (extCost p + 1 + ((W + 3) + 1 +
    (loadCost W p + 1 + (loadCost W (sel 0) + 1 + (loadCost W (sel 1) + 1 + (loadCost W (sel 2) + 1 +
    (loadCost W (sel 3) + 1 + (1 + 1 + (loadCost W (j + 1) + 1 + (pow2Cost W (j + 1) + 1 + ((2 * W + 3) + 1 +
    ((2 * W + 3) + 1 + ((2 * W + 3) + 1 + ((2 * W + 3) + 1 + (2 * W + 3)))))))))))))))))))

section Pro
variable (tw : List Bool) (p : ℕ) (sel : Fin 4 → ℕ) (j : ℕ)

theorem pr8_eq : roles (toSt (pr8 tw p sel j)) = roles (toSt (prS tw p sel j 0)) := by
  unfold prS
  simp only [Nat.not_lt_zero, if_false]
  rfl

theorem prS_step (k : ℕ) (c : Fin 4) (hc : c.val = k) :
    roles (toSt { prS tw p sel j k with S := Function.update (prS tw p sel j k).S c (sel c), ds := Function.update (prS tw p sel j k).ds c (.cells blank (sel c + 1)), us := Function.update (prS tw p sel j k).us c (.cells (PacketsKeys.Pow.u (sel c)) (sel c + 1)), fl := false }) =
      roles (toSt (prS tw p sel j (k + 1))) := by
  have e1 : Function.update (prS tw p sel j k).S c (sel c) = fun d => if d.val < k + 1 then sel d else 0 := by
    funext d; simp only [prS, Function.update_apply]
    by_cases h : d = c
    · subst h; simp; omega
    · rw [if_neg h]
      have : d.val ≠ k := fun e => h (Fin.ext (by omega))
      by_cases h2 : d.val < k
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]
  have e2 : Function.update (prS tw p sel j k).ds c (.cells blank (sel c + 1)) =
      fun d => if d.val < k + 1 then .cells blank (sel d + 1) else bl := by
    funext d; simp only [prS, Function.update_apply]
    by_cases h : d = c
    · subst h; simp; omega
    · rw [if_neg h]
      have : d.val ≠ k := fun e => h (Fin.ext (by omega))
      by_cases h2 : d.val < k
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]
  have e3 : Function.update (prS tw p sel j k).us c (.cells (PacketsKeys.Pow.u (sel c)) (sel c + 1)) =
      fun d => if d.val < k + 1 then .cells (PacketsKeys.Pow.u (sel d)) (sel d + 1)
        else .cells (PacketsKeys.Pow.u (sel d)) 0 := by
    funext d; simp only [prS, Function.update_apply]
    by_cases h : d = c
    · subst h; simp; omega
    · rw [if_neg h]
      have : d.val ≠ k := fun e => h (Fin.ext (by omega))
      by_cases h2 : d.val < k
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]
  rw [e1, e2, e3]
  rfl

end Pro

theorem pro_run (tw : List Bool) (p : ℕ) (sel : Fin 4 → ℕ) (j : ℕ) (hp2 : 2 ≤ p)
    (hsel : ∀ c, sel c < 2 ^ (8 * tw.length + p + p)) (hj : j + 1 < 8 * tw.length + p + p) :
    LRuns (8 * tw.length + p + p) thrPro (proCost (8 * tw.length + p + p) tw.length p j sel)
      (roles (toSt (zIn tw p sel j))) (roles (toSt (zPro tw p sel j))) := by
  set W := 8 * tw.length + p + p with hWd
  have hpW : p < 2 ^ W := lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hjW : j + 1 < 2 ^ W := lt_trans hj Nat.lt_two_pow_self
  have hEW : 2 ^ (j + 1) < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) hj
  have e1 := initOutT (W := W) (zIn tw p sel j) rfl rfl
  have e2 := unfT (W := W) (pr1 tw p sel j) tw rfl rfl rfl
  have e3 := ruleRT (W := W) (pr2 tw p sel j) rfl
  have e4 := appendRT (W := W) (pr3 tw p sel j) tw 1 le_rfl rfl rfl rfl
  have e5 := extR1T (W := W) (pr4 tw p sel j) p (1 + 8 * tw.length) (by omega) rfl rfl rfl
  have e6 := (extR1'T (W := W) (pr5 tw p sel j) p (1 + 8 * tw.length + p) (by omega) rfl rfl rfl).congr_out
    (show roles (toSt { pr5 tw p sel j with rl := .cells (Ruler.rb (1 + 8 * tw.length + p + p)) (1 + 8 * tw.length + p + p), d1' := .cells blank (p + 1), up1' := .cells (PacketsKeys.Pow.u p) (p + 1), fl := false }) =
      roles (toSt (pr6 tw p sel j)) by rw [show 1 + 8 * tw.length + p + p = 8 * tw.length + p + p + 1 by omega]; rfl)
  have e7 := finishRT (W := W) (pr6 tw p sel j) rfl
  have e8 := (loadPT (W := W) (pr7 tw p sel j) rfl p hpW rfl rfl).congr_out (pr8_eq tw p sel j)
  have f0 := (loadST (W := W) (prS tw p sel j 0) rfl 0 (sel 0) (hsel 0) rfl rfl).congr_out (prS_step tw p sel j 0 0 rfl)
  have f1 := (loadST (W := W) (prS tw p sel j 1) rfl 1 (sel 1) (hsel 1) rfl rfl).congr_out (prS_step tw p sel j 1 1 rfl)
  have f2 := (loadST (W := W) (prS tw p sel j 2) rfl 2 (sel 2) (hsel 2) rfl rfl).congr_out (prS_step tw p sel j 2 2 rfl)
  have f3 := (loadST (W := W) (prS tw p sel j 3) rfl 3 (sel 3) (hsel 3) rfl rfl).congr_out (prS_step tw p sel j 3 3 rfl)
  have e13 := moveJD (W := W) (prS tw p sel j 4) rfl
  have e14 := loadJT (W := W) (pr13 tw p sel j) rfl j hjW rfl rfl
  have e15 := pow2T (W := W) (pr14 tw p sel j) rfl (by show j + 1 < W; omega)
  have e16 := cpyE2mT (W := W) (pr15 tw p sel j) rfl hEW
  have e17 := decE2mT (W := W) { pr15 tw p sel j with E2m := 2 ^ (j + 1), fl := false } rfl hEW Nat.one_le_two_pow
  have e18 := cpyEmT (W := W) { { pr15 tw p sel j with E2m := 2 ^ (j + 1), fl := false } with E2m := 2 ^ (j + 1) - 1, fl := false } rfl (lt_of_le_of_lt (Nat.div_le_self _ _) hEW)
  have e19 := decEmT (W := W) { { { pr15 tw p sel j with E2m := 2 ^ (j + 1), fl := false } with E2m := 2 ^ (j + 1) - 1, fl := false } with Em := 2 ^ (j + 1) / 2, fl := false } rfl
    (lt_of_le_of_lt (Nat.div_le_self _ _) hEW) (by show 1 ≤ 2 ^ (j + 1) / 2; rw [pow_succ]; simp; exact Nat.one_le_two_pow)
  have e20 := incBT (W := W) (pr19 tw p sel j) rfl (by show 0 + 1 < 2 ^ W; omega)
  exact e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq (f0.seq (f1.seq (f2.seq (f3.seq (e13.seq
    (e14.seq (e15.seq (e16.seq (e17.seq (e18.seq (e19.seq e20))))))))))))))))))

/-! ## The whole program -/

/-- **The THR mask-bit program.** -/
def thrProg :=
  Composition.machine thrPro (Composition.machine p1Pass (Composition.machine (modP (NO := 29) rB rP rBm rT rMSK)
    (Composition.machine (mInc (NO := 29) rF) (Composition.machine p2Pass (mRew (NR := 24) (NO := 29) oOM oOS)))))

def thrCost (W n p j : ℕ) (sel : Fin 4 → ℕ) (outLen : ℕ) : ℕ :=
  proCost W n p j sel + 1 + (p1PassCost W + 1 + (modCost W + 1 + ((2 * W + 3) + 1 + (p2PassCost W p + 1 +
    (outLen + 1 + 4)))))

theorem ccP_nil (base : Fin 8 → TS) : ccP [] base = base := by
  funext e; unfold ccP; simp

section Main
variable {α : Type} (ar : α → ℕ) (ch : (x : α) → List (ExactThresholdGate (ar x)))

/-- The selected children's magnitudes. -/
def msOf (L : List α) (sel : Fin 4 → ℕ) : List ℕ :=
  List.ofFn (fun i : Fin L.length => if h : i.val < 4 then (if h2 : sel ⟨i.val, h⟩ < (ch L[i]).length then
    childMagnitude ((ch L[i])[sel ⟨i.val, h⟩]'h2) else 0) else 0)

theorem msOf_length (L : List α) (sel : Fin 4 → ℕ) : (msOf ar ch L sel).length = L.length := by
  simp [msOf]

theorem msOf_get (L : List α) (sel S : Fin 4 → ℕ) (hS : S = sel) (i : Fin 4) (hi : i.val < L.length)
    (hs : S i < (ch L[i.val]).length) :
    (msOf ar ch L sel)[i.val]'(by rw [msOf_length]; exact hi) = childMagnitude ((ch L[i.val])[S i]'hs) := by
  subst hS
  simp only [msOf, List.getElem_ofFn]
  rw [dif_pos i.isLt]
  exact dif_pos hs

theorem zPro_S (tw : List Bool) (p : ℕ) (sel : Fin 4 → ℕ) (j : ℕ) : (zPro tw p sel j).S = sel := by
  funext c; simp [zPro, pr19, pr15, pr14, pr13, prS, c.isLt]

theorem ccR_zero (L : List α) (base : Fin 8 → TS) : ccR ar ch L base 0 = ccP (L.map (payOf ar ch)) base := by
  funext e; unfold ccR; simp

theorem thrProg_run (L : List α) (hL : L.length ≤ 4) (p : ℕ) (hp2 : 2 ≤ p) (sel : Fin 4 → ℕ) (j : ℕ)
    (hj : j + 1 < 8 * (twOf ar ch L).length + p + p)
    (hsel : ∀ (i : Fin 4) (hi : i.val < L.length), sel i < (ch L[i.val]).length)
    (hselW : ∀ c, sel c < 2 ^ (8 * (twOf ar ch L).length + p + p))
    (hW : ∀ x ∈ L, (payOf ar ch x).length ≤ 8 * (twOf ar ch L).length + p + p)
    (hAW : ∀ x ∈ L, ar x + 2 < 2 ^ (8 * (twOf ar ch L).length + p + p))
    (hgW : ∀ x ∈ L, (ch x).length < 2 ^ (8 * (twOf ar ch L).length + p + p))
    (hBW : 1 + (msOf ar ch L sel).sum < 2 ^ (8 * (twOf ar ch L).length + p + p))
    (hPP : p * p < 2 ^ (8 * (twOf ar ch L).length + p + p))
    (hP2 : 2 * p ≤ 2 ^ (8 * (twOf ar ch L).length + p + p)) :
    ∃ σ' : Fin (4 + 24 + 29) → TS,
      LRuns (8 * (twOf ar ch L).length + p + p) thrProg
        (thrCost (8 * (twOf ar ch L).length + p + p) (twOf ar ch L).length p j sel
          (outK ar ch L sel (1 + (msOf ar ch L sel).sum) p j 4).length)
        (roles (toSt (zIn (twOf ar ch L) p sel j))) σ' ∧
      σ' (os oOS) = .cells (sf (outK ar ch L sel (1 + (msOf ar ch L sel).sum) p j 4)) 1 ∧
      σ' (os oOM) = .cells (sf (List.replicate (outK ar ch L sel (1 + (msOf ar ch L sel).sum) p j 4).length true)) 1 := by
  set tw := twOf ar ch L with htw
  set W := 8 * tw.length + p + p with hWd
  set ms := msOf ar ch L sel with hms
  set z0 := zPro tw p sel j with hz0
  have hS0 : z0.S = sel := zPro_S tw p sel j
  have hr0 : z0.rl = .ruler := rfl
  -- prologue
  have e1 := pro_run tw p sel j hp2 hselW hj
  -- pass 1
  have hmsl : ms.length = L.length := msOf_length ar ch L sel
  have e2 := p1Pass_run ar ch (W := W) z0 hr0 L hL ms hmsl (fun _ => rfl)
    (by intro i hi; rw [hS0]; exact hsel i hi)
    (fun i hi => msOf_get ar ch L sel z0.S hS0 i hi _)
    hW hAW hgW (by show 1 + ms.sum < 2 ^ W; exact hBW)
  have b12 : roles (toSt (st1 ar ch z0 L ms 0)) = roles (toSt z0) := by
    unfold st1
    rw [List.take_zero, List.map_nil, ccP_nil]
    rfl
  rw [b12] at e2
  -- `Bm := B mod P`, `F := 1`
  set z1a := p1S z0 (.cells (sf tw) (tw.length + 1)) (ccP (L.map (payOf ar ch)) z0.cc) 0 0 0 0 (z0.B + ms.sum) false
    with hz1a
  have e3 := modBT (W := W) z1a rfl (by show 1 + ms.sum < 2 ^ W; exact hBW) (by show 0 < p; omega)
    (by show 2 * p ≤ 2 ^ W; exact hP2) (by omega)
  have e4 := incFT (W := W) { z1a with Bm := z1a.B % z1a.P, T := 0, MSK := 0, fl := false } rfl
    (by show 0 + 1 < 2 ^ W; have := Nat.one_lt_two_pow_iff.mpr (show W ≠ 0 by omega); omega)
  set z1 : TZ := { { z1a with Bm := z1a.B % z1a.P, T := 0, MSK := 0, fl := false } with F := 0 + 1, fl := false }
    with hz1
  -- pass 2
  have hEp : (2 : ℕ) ^ (j + 1) / 2 = 2 ^ j := by rw [pow_succ]; simp
  have e5 := p2Pass_run ar ch (W := W) z1 rfl L z0.cc (fun _ => rfl) (1 + ms.sum) j
    (by intro i hi; show z0.S i < _; rw [hS0]; exact hsel i hi) hW hAW hgW rfl rfl
    (by show 2 ^ (j + 1) / 2 - 1 = 2 ^ j - 1; rw [hEp]) (by show 0 < p; omega) hP2 hPP rfl
    (Nat.pow_lt_pow_right (by norm_num) hj) (by omega)
  have b45 : roles (toSt z1) = roles (toSt (st2 ar ch z1 L z0.cc (1 + ms.sum) j 0)) := by
    unfold st2
    rw [ccR_zero, show min 0 L.length = 0 from rfl, pow_zero, Nat.mod_eq_of_lt (show 1 < z1.P by show 1 < p; omega)]
    rfl
  -- the output rewound
  have e6 := rewOutT (W := W) (st2 ar ch z1 L z0.cc (1 + ms.sum) j 4)
    (outK ar ch L z1.S (1 + ms.sum) z1.P j 4) rfl rfl
  have hall := e1.seq (e2.seq (e3.seq ((e4.congr_out b45).seq (e5.seq e6))))
  have hz1S : z1.S = sel := hS0
  have hz1P : z1.P = p := rfl
  rw [hz1S, hz1P] at hall
  refine ⟨_, hall, ?_, ?_⟩
  · rw [roles_os]; rfl
  · rw [roles_os]; rfl

end Main

end
end NearCubicWires.PacketsKeys.ThrProg


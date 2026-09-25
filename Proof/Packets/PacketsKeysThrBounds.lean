import Proof.Packets.PacketsKeysThrMain

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

/-! ## Words and their values -/

theorem len_le_flatMap' {β γ : Type} (L : List β) (f : β → List γ) (x : β) (hx : x ∈ L) :
    (f x).length ≤ (L.flatMap f).length := by
  rw [List.length_flatMap]
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨x, hx, rfl⟩)

theorem nat_lt_len (n : ℕ) : n < 2 ^ (natWord n).length := by
  have h1 : n < 2 ^ natBitLength n := by
    unfold natBitLength
    exact Nat.lt_pow_succ_log_self Nat.one_lt_two n
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (natBitLength_le_len n))

/-- `a_i < 2^{l_i}` for all `i` gives `1 + Σ a_i ≤ 2^{Σ l_i}`. -/
theorem sum_pow_le : ∀ (ms ls : List ℕ), ms.length = ls.length →
    (∀ i (h1 : i < ms.length) (h2 : i < ls.length), ms[i] + 1 ≤ 2 ^ ls[i]) → ms.sum + 1 ≤ 2 ^ ls.sum
  | [], ls, _, _ => by
    simp only [List.sum_nil, Nat.zero_add]
    exact Nat.one_le_two_pow
  | _ :: _, [], h, _ => by simp at h
  | m :: ms, l :: ls, h, hi => by
    have h0 := hi 0 (by simp) (by simp)
    have ih := sum_pow_le ms ls (by simpa using h) (fun i h1 h2 => hi (i + 1) (by simp; omega) (by simp; omega))
    simp only [List.getElem_cons_zero] at h0
    simp only [List.sum_cons, pow_add]
    have hmul := Nat.mul_le_mul h0 ih
    have e : (m + 1) * (ms.sum + 1) = m * ms.sum + m + ms.sum + 1 := by ring
    rw [e] at hmul
    generalize m * ms.sum = X at hmul
    generalize 2 ^ l * 2 ^ ls.sum = Y at hmul ⊢
    omega

theorem mag_lt {A : ℕ} (g : ExactThresholdGate A) : childMagnitude g + 1 ≤ 2 ^ (exactWord g).length := by
  rw [← zs_mag, exactWord_zs, List.length_flatMap]
  refine sum_pow_le _ _ (by simp) ?_
  intro i h1 h2
  simp only [List.getElem_map]
  rw [intWord_len, pow_succ]
  have := nat_lt_len ((zs g)[i]'(by simpa using h1)).natAbs
  omega

section Gen
variable {α : Type} (ar : α → ℕ) (ch : (x : α) → List (ExactThresholdGate (ar x)))

theorem pay_le_tw (L : List α) (x : α) (hx : x ∈ L) : (payOf ar ch x).length ≤ (twOf ar ch L).length := by
  have h := len_le_flatMap' L (fun x => RepairOrdinary.frame (payOf ar ch x)) x hx
  rw [RepairOrdinary.frame_length] at h
  unfold twOf
  omega

theorem payTot_le (L : List α) : (L.map (fun x => (payOf ar ch x).length)).sum ≤ (twOf ar ch L).length := by
  unfold twOf
  rw [List.length_flatMap]
  apply List.sum_le_sum
  intro x _
  simp only [RepairOrdinary.frame_length]
  omega

theorem ar_lt_pay (x : α) : ar x < 2 ^ (payOf ar ch x).length := by
  refine lt_of_lt_of_le (nat_lt_len (ar x)) (Nat.pow_le_pow_right (by norm_num) ?_)
  unfold payOf
  simp only [List.length_append]
  omega

theorem ch_lt_pay (x : α) : (ch x).length < 2 ^ (payOf ar ch x).length := by
  refine lt_of_lt_of_le (nat_lt_len (ch x).length) (Nat.pow_le_pow_right (by norm_num) ?_)
  unfold payOf
  simp only [List.length_append]
  omega

theorem gate_le_pay (x : α) (g : ExactThresholdGate (ar x)) (hg : g ∈ ch x) :
    (exactWord g).length ≤ (payOf ar ch x).length := by
  have h := len_le_flatMap' (ch x) exactWord g hg
  unfold payOf
  simp only [List.length_append]
  omega

/-- **The stack base fits the top word.** -/
theorem msOf_sum_le (L : List α) (sel : Fin 4 → ℕ) : (msOf ar ch L sel).sum + 1 ≤ 2 ^ (twOf ar ch L).length := by
  have h1 : (msOf ar ch L sel).sum + 1 ≤ 2 ^ (L.map (fun x => (payOf ar ch x).length)).sum := by
    refine sum_pow_le _ _ (by simp [msOf]) ?_
    intro i h1 h2
    have hi : i < L.length := by simpa [msOf] using h1
    simp only [msOf, List.getElem_ofFn, List.getElem_map]
    split_ifs with ha hb
    · exact le_trans (mag_lt _) (Nat.pow_le_pow_right (by norm_num) (gate_le_pay ar ch _ _ (by simp)))
    · exact Nat.one_le_two_pow
    · exact Nat.one_le_two_pow
  exact le_trans h1 (Nat.pow_le_pow_right (by norm_num) (payTot_le ar ch L))

theorem msOf_get' (L : List α) (sel : Fin 4 → ℕ) (i : ℕ) (hi : i < L.length) (h4 : i < 4) (s : ℕ)
    (hs : sel ⟨i, h4⟩ = s) (hsl : s < (ch L[i]).length) :
    (msOf ar ch L sel)[i]'(by rw [msOf_length]; exact hi) = childMagnitude ((ch L[i])[s]'hsl) := by
  simp only [msOf, List.getElem_ofFn]
  rw [dif_pos h4]
  subst hs
  exact dif_pos hsl

/-! ## The output -/

theorem bitsAt_of (L : List α) (S : Fin 4 → ℕ) (B P j c : ℕ) (hc : c < L.length) (h4 : c < 4) (s : ℕ)
    (hs : S ⟨c, h4⟩ = s) (hsl : s < (ch L[c]).length) :
    bitsAt ar ch L S B P j c = (List.ofFn ((ch L[c])[s]'hsl).weight).map (wb (B ^ c % P) P j) := by
  unfold bitsAt
  rw [dif_pos ⟨hc, h4⟩]
  subst hs
  rw [dif_pos hsl]

theorem outK_eq (L : List α) (hL : L.length ≤ 4) (S : Fin 4 → ℕ) (B P j : ℕ) :
    outK ar ch L S B P j 4 = (List.ofFn (fun c : Fin L.length => bitsAt ar ch L S B P j c.val)).flatten := by
  unfold outK
  have e : List.range 4 = List.range L.length ++ (List.range (4 - L.length)).map (fun x => L.length + x) := by
    rw [← List.range_add]
    congr 1
    omega
  rw [e, List.map_append, List.flatten_append]
  have h2 : (((List.range (4 - L.length)).map (fun x => L.length + x)).map (bitsAt ar ch L S B P j)).flatten = [] := by
    rw [List.flatten_eq_nil_iff]
    intro l hl
    simp only [List.map_map, List.mem_map, List.mem_range] at hl
    obtain ⟨c, _, rfl⟩ := hl
    show bitsAt ar ch L S B P j (L.length + c) = []
    unfold bitsAt
    rw [dif_neg (by omega)]
  rw [h2, List.append_nil]
  congr 1
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp

theorem bitsAt_len_le (L : List α) (S : Fin 4 → ℕ) (B P j c : ℕ) (hc : c < L.length) :
    (bitsAt ar ch L S B P j c).length ≤ (payOf ar ch L[c]).length := by
  unfold bitsAt
  split_ifs with h h2
  · simp only [List.length_map, List.length_ofFn]
    exact ar_le_pay ar ch _ (List.ne_nil_of_length_pos (by omega))
  · simp
  · simp

theorem outK_len_le (L : List α) (hL : L.length ≤ 4) (S : Fin 4 → ℕ) (B P j : ℕ) :
    (outK ar ch L S B P j 4).length ≤ (twOf ar ch L).length := by
  rw [outK_eq ar ch L hL, List.length_flatten, List.map_ofFn, List.sum_ofFn]
  refine le_trans ?_ (payTot_le ar ch L)
  have e : (L.map (fun x => (payOf ar ch x).length)).sum = ∑ c : Fin L.length, (payOf ar ch L[c]).length := by
    rw [← List.sum_ofFn]
    congr 1
    apply List.ext_getElem (by simp)
    intro n h1 h2
    simp
  rw [e]
  apply Finset.sum_le_sum
  intro c _
  exact bitsAt_len_le ar ch L S B P j c.val c.isLt

/-! ## The run with structural premises only -/

theorem pow_facts (m p : ℕ) (hp2 : 2 ≤ p) :
    2 ^ m + 2 ≤ 2 ^ (8 * m + p + p) ∧ 2 ^ m < 2 ^ (8 * m + p + p) ∧ p * p < 2 ^ (8 * m + p + p) ∧
      2 * p ≤ 2 ^ (8 * m + p + p) := by
  have hp : p < 2 ^ p := Nat.lt_two_pow_self
  have e1 : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_add]; ring
  have h1 : 2 ^ (m + 2) ≤ 2 ^ (8 * m + p + p) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h0 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have e2 : 2 ^ (p + p) = 2 ^ p * 2 ^ p := pow_add 2 p p
  have h2 : 2 ^ (p + p) ≤ 2 ^ (8 * m + p + p) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpp : p * p < 2 ^ p * 2 ^ p := Nat.mul_self_lt_mul_self hp
  have e3 : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ]; ring
  have h3 : 2 ^ (p + 1) ≤ 2 ^ (8 * m + p + p) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- **The THR program's run**, at `W = 8|tw| + p + p`, from structural premises: at most four circuits, a prime-sized
`p ≥ 2`, the digit index below `p`, the selections valid and bounded by the top word. -/
theorem thrRun (L : List α) (hL : L.length ≤ 4) (p : ℕ) (hp2 : 2 ≤ p) (sel : Fin 4 → ℕ) (j : ℕ) (hj : j + 1 ≤ p)
    (hsel : ∀ (i : Fin 4) (hi : i.val < L.length), sel i < (ch L[i.val]).length)
    (hsl : ∀ c, sel c ≤ (twOf ar ch L).length) :
    ∃ σ' : Fin (4 + 24 + 29) → TS,
      LRuns (8 * (twOf ar ch L).length + p + p) thrProg
        (thrCost (8 * (twOf ar ch L).length + p + p) (twOf ar ch L).length p j sel
          (outK ar ch L sel (1 + (msOf ar ch L sel).sum) p j 4).length)
        (roles (toSt (zIn (twOf ar ch L) p sel j))) σ' ∧
      σ' (os oOS) = .cells (sf (outK ar ch L sel (1 + (msOf ar ch L sel).sum) p j 4)) 1 ∧
      σ' (os oOM) = .cells (sf (List.replicate (outK ar ch L sel (1 + (msOf ar ch L sel).sum) p j 4).length true)) 1 := by
  obtain ⟨f1, f2, f3, f4⟩ := pow_facts (twOf ar ch L).length p hp2
  have hm : (twOf ar ch L).length < 2 ^ (twOf ar ch L).length := Nat.lt_two_pow_self
  refine thrProg_run ar ch L hL p hp2 sel j (by omega) hsel (fun c => by have := hsl c; omega)
    (fun x hx => by have := pay_le_tw ar ch L x hx; omega) ?_ ?_ ?_ f3 f4
  · intro x hx
    have h1 := ar_lt_pay ar ch x
    have h2 : 2 ^ (payOf ar ch x).length ≤ 2 ^ (twOf ar ch L).length :=
      Nat.pow_le_pow_right (by norm_num) (pay_le_tw ar ch L x hx)
    omega
  · intro x hx
    have h1 := ch_lt_pay ar ch x
    have h2 : 2 ^ (payOf ar ch x).length ≤ 2 ^ (twOf ar ch L).length :=
      Nat.pow_le_pow_right (by norm_num) (pay_le_tw ar ch L x hx)
    omega
  · have := msOf_sum_le ar ch L sel
    omega

end Gen

/-! ## The step count -/

theorem proCost_mono (W n p j : ℕ) (sel : Fin 4 → ℕ) (hn : n ≤ W) (hp : p ≤ W) (hj : j ≤ W)
    (hs : ∀ c, sel c ≤ W) : proCost W n p j sel ≤ proCost W W W W (fun _ => W) := by
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  have h3 := hs 3
  unfold proCost loadCost extCost pow2Cost
  gcongr

theorem p2PassCost_mono (W P : ℕ) (hP : P ≤ W) : p2PassCost W P ≤ p2PassCost W W := by
  unfold p2PassCost p2BlockCost p2BodyCost wBodyCost testCost
  gcongr

theorem thrCost_top (W : ℕ) : thrCost W W W W (fun _ => W) W ≤ 100000 * (W + 1) ^ 3 := by
  unfold thrCost proCost p1PassCost p1BlockCost p1BodyCost p2PassCost p2BlockCost p2BodyCost wBodyCost fixCost
    cleanCost testCost seekCost skipAllCost skipAllBodyCost skipBodyCost sumBodyCost modCost modBodyCost loadCost
    extCost pow2Cost
  ring_nf
  nlinarith [Nat.zero_le W, Nat.zero_le (W ^ 2), Nat.zero_le (W ^ 3)]

/-- **The THR program's step count**: at most `100000·(W+1)^3` when every loop count is at most `W`. -/
theorem thrCost_le (W n p j o : ℕ) (sel : Fin 4 → ℕ) (hn : n ≤ W) (hp : p ≤ W) (hj : j ≤ W) (hs : ∀ c, sel c ≤ W)
    (ho : o ≤ W) : thrCost W n p j sel o ≤ 100000 * (W + 1) ^ 3 := by
  refine le_trans ?_ (thrCost_top W)
  have h1 := proCost_mono W n p j sel hn hp hj hs
  have h2 := p2PassCost_mono W p hp
  unfold thrCost
  omega

end
end NearCubicWires.PacketsKeys.ThrProg


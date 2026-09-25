import Proof.Packets.PacketsSetupWords
import Proof.Packets.PacketFamilyScrubAdapter

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.PacketsGlue.MoveOne
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch

/-- One step: move the head of tape `k` right; nothing written. -/
def machine (T : ℕ) (k : Fin T) : Machine T 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some ⟨1, fun _ => none, fun i => if i = k then .right else .stay⟩ else none

theorem run (T : ℕ) (k : Fin T) (H : Fin T → ℕ) (A : Fin T → List Bool) :
    Step (machine T k) 1 H A (Function.update H k (H k + 1)) A := by
  have hs : step (machine T k) ⟨0, H, A⟩ = some ⟨1, Function.update H k (H k + 1), A⟩ := by
    simp [step, machine]
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i = k
      · subst hi; simp [applyAction, HeadMove.apply]
      · simp [applyAction, HeadMove.apply, hi]
    · funext i; simp [applyAction]
  have t := Timed.single (p := machine T k) (by simp [machine]) hs
  obtain ⟨r, hr, hf, hsteps⟩ := t.run (by simp [machine])
  exact ⟨r, hr, by rw [hf], by rw [hf], by omega⟩

end NearCubicWires.PacketsGlue.MoveOne

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.BlockPlatform NearCubicWires.PacketsConstruction
open NearCubicWires.PacketsGlue.LexSucc
noncomputable section

/-! ## Polynomially costed word composition -/

/-- `thenWord`, with the side condition from a polynomial cost of the map. -/
def UnaryStage.thenWordP {a : DecompositionAlgorithm} {v : Request → ℕ} {g : ℕ → List Bool}
    (s : UnaryStage a v) (m : WordMap g) (cm dm : ℕ) (hm : ∀ x, m.cost x ≤ cm * (x + 3) ^ dm) :
    WordStage a (fun r => g (v r)) :=
  s.thenWord m (cm * (s.coefficient + 7) ^ dm) ((s.degree + 1) * dm) (by
    intro r
    have hb := s.value_bound r
    have hp : (v r + 3) ^ dm ≤ ((s.coefficient + 7) * (r.smallSize a) ^ (s.degree + 1)) ^ dm :=
      Nat.pow_le_pow_left hb dm
    have e : ((s.coefficient + 7) * (r.smallSize a) ^ (s.degree + 1)) ^ dm =
        (s.coefficient + 7) ^ dm * (r.smallSize a) ^ ((s.degree + 1) * dm) := by
      rw [mul_pow, ← pow_mul]
    rw [e] at hp
    calc m.cost (v r) ≤ cm * (v r + 3) ^ dm := hm (v r)
      _ ≤ cm * ((s.coefficient + 7) ^ dm * (r.smallSize a) ^ ((s.degree + 1) * dm)) :=
          Nat.mul_le_mul_left _ hp
      _ = cm * (s.coefficient + 7) ^ dm * (r.smallSize a) ^ ((s.degree + 1) * dm) := by
          rw [Nat.mul_assoc])

/-- `pairW`, with the side condition from a polynomial cost of the map. -/
def UnaryStage.pairWP {a : DecompositionAlgorithm} {v1 v2 : Request → ℕ} {g : ℕ → ℕ → List Bool}
    (s1 : UnaryStage a v1) (s2 : UnaryStage a v2) (m : WordMap2 g) (cm dm : ℕ)
    (hm : ∀ x y, m.cost x y ≤ cm * (x + y + 3) ^ dm) : WordStage a (fun r => g (v1 r) (v2 r)) :=
  s1.pairW s2 m (cm * (s1.coefficient + s2.coefficient + 14) ^ dm) ((s1.degree + s2.degree + 2) * dm) (by
    intro r
    have b1 := s1.value_bound r
    have b2 := s2.value_bound r
    set D := s1.degree + s2.degree + 2
    have p1 := pow_le_pow_small a r (s1.degree + 1) D (by omega)
    have p2 := pow_le_pow_small a r (s2.degree + 1) D (by omega)
    have q1 := Nat.mul_le_mul_left (s1.coefficient + 7) p1
    have q2 := Nat.mul_le_mul_left (s2.coefficient + 7) p2
    have hb : v1 r + v2 r + 3 ≤ (s1.coefficient + s2.coefficient + 14) * (r.smallSize a) ^ D := by
      have e : (s1.coefficient + s2.coefficient + 14) * (r.smallSize a) ^ D =
          (s1.coefficient + 7) * (r.smallSize a) ^ D + (s2.coefficient + 7) * (r.smallSize a) ^ D := by ring
      rw [e]; omega
    have hp := Nat.pow_le_pow_left hb dm
    have e : ((s1.coefficient + s2.coefficient + 14) * (r.smallSize a) ^ D) ^ dm =
        (s1.coefficient + s2.coefficient + 14) ^ dm * (r.smallSize a) ^ (D * dm) := by
      rw [mul_pow, ← pow_mul]
    rw [e] at hp
    calc m.cost (v1 r) (v2 r) ≤ cm * (v1 r + v2 r + 3) ^ dm := hm _ _
      _ ≤ cm * ((s1.coefficient + s2.coefficient + 14) ^ dm * (r.smallSize a) ^ (D * dm)) :=
          Nat.mul_le_mul_left _ hp
      _ = cm * (s1.coefficient + s2.coefficient + 14) ^ dm * (r.smallSize a) ^ (D * dm) := by
          rw [Nat.mul_assoc])

theorem zero_cost (x : ℕ) : zeroWordMap.cost x ≤ 8 * (x + 3) ^ 1 := by
  change 4 * x + 4 ≤ _; rw [pow_one]; omega

theorem isZero_cost (x : ℕ) : isZeroMap.cost x ≤ 4 * (x + 3) ^ 1 := by
  change 2 * 1 + 2 ≤ _; rw [pow_one]; omega

theorem flag_cost (x y : ℕ) : flagWordMap2.cost x y ≤ 16 * (x + y + 3) ^ 1 := by
  change 2 * (2 * y + 1) + 2 + 1 + (4 * x + 4) ≤ _; rw [pow_one]; omega

theorem cmp_cost (x : ℕ) : cmpWordMap.cost x ≤ 6 * (x + 3) ^ 1 := by
  change 2 * (x + 2) + 2 ≤ _; rw [pow_one]; omega

/-! ## The start digits -/

theorem zero_zero : ∀ (spec : List (Level (Fin 8))), zero spec (fun _ => 0) = fun _ => 0
  | [] => rfl
  | l :: ls => by
    simp only [zero]
    have : Function.update (fun _ : Fin 8 => (0 : ℕ)) l.field 0 = fun _ => 0 := by
      funext x; by_cases h : x = l.field <;> simp [h]
    rw [this]
    exact zero_zero ls

/-- The first key's digits: all `0`, or the done code when there is no key. -/
theorem start_digits (a : DecompositionAlgorithm) (r : Request) (i : Fin 8) :
    keyDigits a r (rcKeys a r)[0]? i = if i.val = 7 ∧ rcKeys a r = [] then 1 else 0 := by
  by_cases h : rcKeys a r = []
  · rw [h]
    simp [keyDigits_none]
  · obtain ⟨k0, ks, hk⟩ := List.exists_cons_of_ne_nil h
    have hd := digits_eq a r
    have hw := (enum_next (cursorSpec a r) (cursorSpec_wf a r) (cursorSpec_pos a r h) (fun _ => 0)).2.2
    rw [← hd, hk] at hw
    simp only [List.map_cons, List.head?_cons, Option.some.injEq] at hw
    rw [hk]
    simp only [List.getElem?_cons_zero]
    rw [hw, zero_zero]
    simp [h]

theorem rows_zero (a : DecompositionAlgorithm) (r : Request) :
    ((r.family a).rows.length = 0) ↔ rcKeys a r = [] := by
  rw [← (rcFiveKeys a).length_eq r]
  exact List.length_eq_zero_iff

/-! ## The ten words -/

section Vec
variable (a : DecompositionAlgorithm) {R : Request → ℕ} (WS : UnaryStage a (fieldWidth a))
  (rowsS : UnaryStage a (fun r => (r.family a).rows.length)) (RS : UnaryStage a R)

/-- `frame (binary W 0)`. -/
def zeroW : WordStage a (fun r => RepairOrdinary.frame (SignedSortKey.binary (fieldWidth a r) 0)) :=
  WS.thenWordP zeroWordMap 8 1 zero_cost

/-- `frame (binary W [rows = 0])` (as the normalizer's word). -/
def flagW : WordStage a (fun r => RepairOrdinary.frame (ClockNormalize.resize (fieldWidth a r)
    (List.replicate (if (r.family a).rows.length = 0 then 1 else 0) true))) :=
  WS.pairWP (rowsS.thenMapP isZeroMap 4 1 isZero_cost) flagWordMap2 16 1 flag_cost

/-- `CompareMachine.word rows`. -/
def rowW : WordStage a (fun r => RepairSource.VerifierDecoding.CompareMachine.word ((r.family a).rows.length)) :=
  rowsS.thenWordP cmpWordMap 6 1 cmp_cost

end Vec

/-! ## The dock of the masked vector into the setup tapes -/

/-! ## The setup bank, by value -/

/-- `Fin.addCases` over the setup's three blocks, by value. -/
theorem ac3 {α : Type} {t : ℕ} (X : Fin t → α) (Y : Fin 2 → α) (Z : Fin 1 → α) (i : Fin (t + 2 + 1)) :
    Fin.addCases (Fin.addCases X Y) Z i =
      if h : i.val < t then X ⟨i.val, h⟩ else if i.val = t then Y 0 else if i.val = t + 1 then Y 1 else Z 0 := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.addCases_left]
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · rw [Fin.addCases_left]
      have : ((Fin.castAdd 1 (Fin.castAdd 2 k)) : Fin (t + 2 + 1)).val = k.val := rfl
      rw [dif_pos (by rw [this]; exact k.isLt)]
      rfl
    · rw [Fin.addCases_right]
      have : ((Fin.castAdd 1 (Fin.natAdd t k)) : Fin (t + 2 + 1)).val = t + k.val := rfl
      rw [dif_neg (by rw [this]; omega)]
      fin_cases k
      · simp [this]
      · simp [this]
  · rw [Fin.addCases_right]
    have : ((Fin.natAdd (t + 2) j) : Fin (t + 2 + 1)).val = t + 2 + j.val := rfl
    rw [dif_neg (by rw [this]; omega), if_neg (by rw [this]; omega), if_neg (by rw [this]; omega)]
    rw [Fin.eq_zero j]

section Run
variable (a : DecompositionAlgorithm) (w : ℕ) (R : Request → ℕ) (cR dR : ℕ)
  (hR : ∀ r, R r ≤ cR * (r.smallSize a) ^ dR)
  (WS : UnaryStage a (fieldWidth a)) (rowsS : UnaryStage a (fun r => (r.family a).rows.length))
  (RS : UnaryStage a R)

/-- The scratch set of `digitLayout`, on the setup's tapes. -/
def scr (w : ℕ) : Fin (10 + w + 2 + 1) → Bool := fun i => decide (10 ≤ i.val ∧ i.val < 10 + w)

/-- The false blanks: only the scrub log is padded (to `R + 1`). -/
def setupBlank (w : ℕ) (R : Request → ℕ) (r : Request) (i : Fin (10 + w + 2 + 1)) : ℕ :=
  if i.val = 10 + w then R r + 1 else 0

/-- `Fin.addCases` of one extra tape, by value. -/
theorem ac2 {α : Type} {t : ℕ} (X : Fin t → α) (Y : Fin 1 → α) (i : Fin (t + 1)) :
    Fin.addCases X Y i = if h : i.val < t then X ⟨i.val, h⟩ else Y 0 := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.addCases_left]
    have : ((Fin.castAdd 1 j) : Fin (t + 1)).val = j.val := rfl
    rw [dif_pos (by rw [this]; exact j.isLt)]
    rfl
  · rw [Fin.addCases_right]
    have : ((Fin.natAdd t j) : Fin (t + 1)).val = t + j.val := rfl
    rw [dif_neg (by rw [this]; omega), Fin.eq_zero j]

/-- **The exit bank, by value.** -/
def goalVal (r : Request) (i : Fin (10 + w + 2 + 1)) : List Bool :=
  if i.val = 0 then RepairOrdinary.frame (Request.input a r)
  else if 2 ≤ i.val ∧ i.val ≤ 8 then RepairOrdinary.frame (SignedSortKey.binary (fieldWidth a r) 0)
  else if i.val = 9 then RepairOrdinary.frame (SignedSortKey.binary (fieldWidth a r)
    (if (r.family a).rows.length = 0 then 1 else 0))
  else if 10 ≤ i.val ∧ i.val < 10 + w then List.replicate (R r) false
  else if i.val = 10 + w then List.replicate (R r + 1) false
  else if i.val = 10 + w + 1 then List.replicate (R r) true
  else if i.val = 10 + w + 2 then RepairSource.VerifierDecoding.CompareMachine.word ((r.family a).rows.length)
  else []

theorem gv0 (r : Request) (i : Fin (10 + w + 2 + 1)) (h : i.val = 0) :
    goalVal a w R r i = RepairOrdinary.frame (Request.input a r) := by
  unfold goalVal; rw [if_pos h]

theorem gv1 (r : Request) (i : Fin (10 + w + 2 + 1)) (h : i.val = 1) : goalVal a w R r i = [] := by
  unfold goalVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

theorem gvZ (r : Request) (i : Fin (10 + w + 2 + 1)) (h : 2 ≤ i.val ∧ i.val ≤ 8) :
    goalVal a w R r i = RepairOrdinary.frame (SignedSortKey.binary (fieldWidth a r) 0) := by
  unfold goalVal; rw [if_neg (by omega), if_pos h]

theorem gv9 (r : Request) (i : Fin (10 + w + 2 + 1)) (h : i.val = 9) :
    goalVal a w R r i = RepairOrdinary.frame (SignedSortKey.binary (fieldWidth a r)
      (if (r.family a).rows.length = 0 then 1 else 0)) := by
  unfold goalVal; rw [if_neg (by omega), if_neg (by omega), if_pos h]

theorem gvS (r : Request) (i : Fin (10 + w + 2 + 1)) (h : 10 ≤ i.val ∧ i.val < 10 + w) :
    goalVal a w R r i = List.replicate (R r) false := by
  unfold goalVal; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]

theorem gvL (r : Request) (i : Fin (10 + w + 2 + 1)) (h : i.val = 10 + w) :
    goalVal a w R r i = List.replicate (R r + 1) false := by
  unfold goalVal; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]

theorem gvD (r : Request) (i : Fin (10 + w + 2 + 1)) (h : i.val = 10 + w + 1) :
    goalVal a w R r i = List.replicate (R r) true := by
  unfold goalVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]

theorem gvC (r : Request) (i : Fin (10 + w + 2 + 1)) (h : i.val = 10 + w + 2) :
    goalVal a w R r i = RepairSource.VerifierDecoding.CompareMachine.word ((r.family a).rows.length) := by
  unfold goalVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos h]

/-- The layout's bank with empty output, by value. -/
theorem bank_val (r : Request) (c : Option (rcKey a r)) (j : Fin (10 + w)) :
    (digitLayout a w R cR dR hR).bank r c [] j =
      if j.val = 1 then [] else if h10 : 10 ≤ j.val then List.replicate (R r) false
      else if h : 2 ≤ j.val then RepairOrdinary.frame (SignedSortKey.binary (fieldWidth a r)
        (keyDigits a r c ⟨j.val - 2, by omega⟩))
      else if j.val = 0 then RepairOrdinary.frame (Request.input a r) else [] := by
  have := j.isLt
  simp only [Layout.bank, digitLayout, Fin.ext_iff, decide_eq_true_eq]
  by_cases h1 : j.val = 1
  · simp [h1]
  · by_cases hs : 10 ≤ j.val
    · simp [h1, hs]
    · by_cases h2 : 2 ≤ j.val
      · simp only [h1, hs, h2, if_false, dif_neg, not_false_eq_true, true_and, dite_true, if_true, dif_pos]
        have hlt : j.val < 10 := by omega
        rw [if_pos hlt, dif_pos hlt]
        rfl
      · have h0 : j.val = 0 ∨ j.val = 1 := by omega
        simp [h1, hs, h2]

/-- The consumer's exit bank is `goalVal`. -/
theorem target_eq (r : Request) :
    Fin.addCases (Fin.addCases ((digitLayout a w R cR dR hR).bank r (rcKeys a r)[0]? [])
      ((blockScrubForm (10 + w) (digitLayout a w R cR dR hR).scratch).residentA (R r)))
      (fun _ : Fin 1 => RepairSource.VerifierDecoding.CompareMachine.word (rcKeys a r).length) = goalVal a w R r := by
  funext i
  rw [ac3]
  have := i.isLt
  by_cases hl : i.val < 10 + w
  · rw [dif_pos hl, bank_val]
    simp only [Fin.val_mk]
    by_cases h1 : i.val = 1
    · rw [if_pos h1, gv1 a w R r i h1]
    · rw [if_neg h1]
      by_cases hs : 10 ≤ i.val
      · rw [dif_pos hs, gvS a w R r i ⟨hs, hl⟩]
      · rw [dif_neg hs]
        by_cases h2 : 2 ≤ i.val
        · rw [dif_pos h2]
          have hk := start_digits a r ⟨i.val - 2, by omega⟩
          simp only [Fin.val_mk] at hk
          refine (congrArg (fun x => RepairOrdinary.frame (SignedSortKey.binary (fieldWidth a r) x)) hk).trans ?_
          by_cases h9 : i.val = 9
          · rw [gv9 a w R r i h9]
            have hz := rows_zero a r
            by_cases hk : rcKeys a r = []
            · rw [if_pos ⟨by omega, hk⟩, if_pos (hz.mpr hk)]
            · rw [if_neg (fun h => hk h.2), if_neg (fun h => hk (hz.mp h))]
          · rw [if_neg (fun h => by omega), gvZ a w R r i ⟨h2, by omega⟩]
        · rw [dif_neg h2]
          have h0 : i.val = 0 := by omega
          rw [if_pos h0, gv0 a w R r i h0]
  · rw [dif_neg hl]
    by_cases hL : i.val = 10 + w
    · rw [if_pos hL, gvL a w R r i hL]; rfl
    · rw [if_neg hL]
      by_cases hD : i.val = 10 + w + 1
      · rw [if_pos hD, gvD a w R r i hD]; rfl
      · rw [if_neg hD, gvC a w R r i (by omega),
          show (rcKeys a r).length = (r.family a).rows.length from (rcFiveKeys a).length_eq r]

/-- The padded entry. -/
def B0 (r : Request) : Fin (10 + w + 2 + 1) → List Bool :=
  fun i => ZeroPadding.pad (setupBlank w R r i) (inBank (10 + w + 2 + 1) (Request.input a r) i)

theorem B0_val (r : Request) (i : Fin (10 + w + 2 + 1)) : B0 a w R r i =
    if i.val = 0 then RepairOrdinary.frame (Request.input a r)
    else if i.val = 10 + w then List.replicate (R r + 1) false else [] := by
  simp only [B0, setupBlank, inBank_val]
  by_cases h0 : i.val = 0
  · rw [if_pos h0, if_neg (by omega), if_pos h0]; simp [ZeroPadding.pad]
  · rw [if_neg h0, if_neg h0]
    by_cases hl : i.val = 10 + w
    · rw [if_pos hl, if_pos hl]; simp [ZeroPadding.pad]
    · rw [if_neg hl, if_neg hl]; simp [ZeroPadding.pad]

end Run

end
end NearCubicWires.PacketsGlue.RequestMeta


import Proof.Packets.PacketsKeysPow
import Proof.Packets.PacketsDock

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsKeys.Pow
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.PacketsMeta NearCubicWires.PacketsKeys
open PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketFamilyParent NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires.PacketsConstruction
noncomputable section

/-- `Pow.prog`'s step count. -/
def pcost (x e w : ℕ) : ℕ :=
  1 + 1 + ((w + 1) * (1 + 1 + 2) + 1 + ((w + 3) + 1 + ((x + 1) * (1 + (2 * w + 3) + 2) + 1 +
    ((e + 1) * (1 + (2 * w + 3) + 2) + 1 + ((2 * w + 3) + 1 +
    ((e + 1) * ((2 * w + 3) + ((13 * w * w + 60 * w + 40) + 1 + ((2 * w + 3) + 1 + (2 * w + 3))) + 2) + 1 +
    (x ^ e + 1) * ((2 * w + 3) + (2 * w + 3 + 1 + 1) + 2)))))))

theorem readTapeBit_rep (n j : ℕ) : readTapeBit (List.replicate n true) j = decide (j < n) := by
  unfold readTapeBit
  by_cases h : j < n
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]; simp [h]
  · rw [List.getD_eq_default _ _ (by simpa using h)]; simp [h]

theorem tr_in (W x e w : ℕ) (j : Fin 16) (hj : j.val < 3) :
    TR W (pv x e w s0 j) 0 (List.replicate (if j.val = 2 then w else if j.val = 1 then e else x) true) := by
  fin_cases j
  · exact ⟨rfl, fun k => by simp [readTapeBit_rep, u]⟩
  · exact ⟨rfl, fun k => by simp [readTapeBit_rep, u]⟩
  · exact ⟨rfl, fun k => by simp [readTapeBit_rep, u]⟩
  all_goals simp at hj

theorem tr_nil (W x e w : ℕ) (j : Fin 16) (hj : 3 ≤ j.val) : TR W (pv x e w s0 j) 0 [] := by
  fin_cases j <;> simp_all [pv, s0, TR, readTapeBit, blank]

section Stage
variable {a : DecompositionAlgorithm} {vx ve vw : Request → ℕ}
  (sx : UnaryStage a vx) (se : UnaryStage a ve) (sw : UnaryStage a vw)

/-- The three words. -/
def vec3 := (((VecStage.nil a (fun _ _ => [])).snoc sx.toWord).snoc se.toWord).snoc sw.toWord

/-- Vector slots: `0 ↦ 0`, outputs `1,2,3 ↦ 2,3,4`, private `4 + i ↦ 5 + i`. -/
def vSlot (E : ℕ) (j : Fin (1 + 3 + E)) : Fin (2 + (15 + E)) :=
  ⟨if j.val = 0 then 0 else j.val + 1, by have := j.isLt; split_ifs <;> omega⟩

/-- Program slots: `0,1,2 ↦ 2,3,4`, `3 ↦ 1`, work `4 + i ↦ 5 + E + i`. -/
def pSlot (E : ℕ) (j : Fin 16) : Fin (2 + (15 + E)) :=
  ⟨if j.val < 3 then j.val + 2 else if j.val = 3 then 1 else j.val + 1 + E, by
    have := j.isLt; split_ifs <;> omega⟩

theorem vSlot_inj (E : ℕ) : Function.Injective (vSlot E) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [vSlot] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem pSlot_inj (E : ℕ) : Function.Injective (pSlot E) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [pSlot] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The composed machine, before the reset. -/
def core := Composition.machine (RecoveryFocus.machine (vSlot (vec3 sx se sw).extra) (vec3 sx se sw).machine)
  (RecoveryFocus.machine (pSlot (vec3 sx se sw).extra) prog)

theorem core_run (r : Request) (hx : vx r < 2 ^ vw r) (he : ve r < 2 ^ vw r) (hp : vx r ^ ve r < 2 ^ vw r)
    (hw : 1 ≤ vw r) :
    ∃ (H' : Fin (2 + (15 + (vec3 sx se sw).extra)) → ℕ) (A' : Fin (2 + (15 + (vec3 sx se sw).extra)) → List Bool),
      Step (core sx se sw) ((vec3 sx se sw).cost r + 1 + pcost (vx r) (ve r) (vw r)) (fun _ => 0)
        (inBank (2 + (15 + (vec3 sx se sw).extra)) (Request.input a r)) H' A' ∧
      A' ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r) ∧
      A' ⟨1, by omega⟩ = List.replicate (vx r ^ ve r) true := by
  set V := vec3 sx se sw with hV
  set E := V.extra with hE
  obtain ⟨H1, A1, s1, h0A, h0H, hout⟩ := V.run r
  obtain ⟨H2, A2, st2, hs2, ho2⟩ := Dock.lift s1 (vSlot E) (vSlot_inj E) (fun _ => 0) (fun _ => 0)
    (inBank (2 + (15 + E)) (Request.input a r)) (by
      intro j
      refine ⟨rfl, ?_⟩
      rw [ZeroPadding.pad_zero]
      simp only [inBank, vSlot]
      by_cases hj : j.val = 0 <;> simp [hj])
  -- the three words sit on tapes 2, 3, 4
  have hw3 : ∀ (k : ℕ) (hk : k < 3), A2 ⟨k + 2, by omega⟩ = List.replicate
      ((if k = 2 then vw r else if k = 1 then ve r else vx r)) true ∧ H2 ⟨k + 2, by omega⟩ = 0 := by
    intro k hk
    have hs := hs2 ⟨k + 1, by omega⟩
    have he : vSlot E ⟨k + 1, by omega⟩ = ⟨k + 2, by omega⟩ := Fin.ext (by simp [vSlot])
    rw [he] at hs
    obtain ⟨o1, o2⟩ := hout k hk
    rw [hs.1, hs.2, ZeroPadding.pad_zero, o1, o2]
    refine ⟨?_, rfl⟩
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with h | h | h <;> subst h <;> rfl
  have hother : ∀ i : Fin (2 + (15 + E)), (i.val = 1 ∨ 5 + E ≤ i.val) → A2 i = [] ∧ H2 i = 0 := by
    intro i hi
    have hn : ∀ j, vSlot E j ≠ i := by
      intro j hj
      have hv := congrArg Fin.val hj
      simp only [vSlot] at hv
      have := j.isLt
      split_ifs at hv <;> omega
    obtain ⟨o1, o2⟩ := ho2 i hn
    rw [o1, o2]
    refine ⟨?_, rfl⟩
    simp only [inBank]
    rw [if_neg (by omega)]
  have h0 : A2 ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r) := by
    have hs := hs2 ⟨0, by omega⟩
    have he : vSlot E ⟨0, by omega⟩ = ⟨0, by omega⟩ := Fin.ext (by simp [vSlot])
    rw [he] at hs
    rw [hs.2, ZeroPadding.pad_zero, h0A]
  -- the program, on its slots
  obtain ⟨s, hl, hout'⟩ := prog_run (vx r) (ve r) (vw r) hx he hp hw
  have htr : ∀ j, TR (vw r) (pv (vx r) (ve r) (vw r) s0 j) (H2 (pSlot E j)) (A2 (pSlot E j)) := by
    intro j
    by_cases hj : j.val < 3
    · have hs : pSlot E j = ⟨j.val + 2, by omega⟩ := Fin.ext (by simp [pSlot, hj])
      obtain ⟨o1, o2⟩ := hw3 j.val hj
      rw [hs, o1, o2]
      exact tr_in (vw r) (vx r) (ve r) (vw r) j hj
    · have hn := hother (pSlot E j) (by simp only [pSlot]; split_ifs <;> omega)
      rw [hn.1, hn.2]
      exact tr_nil (vw r) (vx r) (ve r) (vw r) j (by omega)
  obtain ⟨H3, A3, st3, h3⟩ := hl (fun j => H2 (pSlot E j)) (fun j => A2 (pSlot E j)) htr
  obtain ⟨H4, A4, st4, hs4, ho4⟩ := Dock.lift st3 (pSlot E) (pSlot_inj E) (fun _ => 0) H2 A2 (by
    intro j; exact ⟨rfl, by rw [ZeroPadding.pad_zero]⟩)
  refine ⟨H4, A4, st2.seq st4, ?_, ?_⟩
  · have hn : ∀ j, pSlot E j ≠ ⟨0, by omega⟩ := by
      intro j hj
      have hv := congrArg Fin.val hj
      simp only [pSlot] at hv
      split_ifs at hv <;> omega
    rw [(ho4 _ hn).2, h0]
  · have he : pSlot E 3 = ⟨1, by omega⟩ := Fin.ext (by simp [pSlot])
    have hs := hs4 3
    rw [he, ZeroPadding.pad_zero] at hs
    have ht := h3 3
    have hA3 : A3 3 = List.replicate s.out true := ht.2
    rw [hs.2, hA3, hout']

theorem inBank_succ (T : ℕ) (hT : 1 ≤ T) (wd : List Bool) :
    Fin.addCases (inBank T wd) (fun _ : Fin 1 => ([] : List Bool)) = inBank (T + 1) wd := by
  funext i
  refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
  · rw [Fin.addCases_left]; simp [inBank]
  · rw [Fin.addCases_right]; simp [inBank]; omega

theorem heads_succ (T : ℕ) : Fin.addCases (fun _ : Fin T => (0 : ℕ)) (fun _ : Fin 1 => (0 : ℕ)) = fun _ => 0 := by
  funext i
  refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
  · rw [Fin.addCases_left]
  · rw [Fin.addCases_right]

/-- **`x^e` as one stage**, from the stages of `x`, `e` and a width `w` with `x, e, x^e < 2^w`, `1 ≤ w`, and a
polynomial bound on the program's step count at the actual values. -/
def powStage (cP dP : ℕ)
    (hgood : ∀ r, vx r < 2 ^ vw r ∧ ve r < 2 ^ vw r ∧ vx r ^ ve r < 2 ^ vw r ∧ 1 ≤ vw r)
    (hpc : ∀ r, pcost (vx r) (ve r) (vw r) ≤ cP * (r.smallSize a) ^ dP) :
    UnaryStage a (fun r => vx r ^ ve r) where
  extra := 15 + (vec3 sx se sw).extra + 1
  states := _
  machine := MaskedReset.machine (core sx se sw) (fun _ => true)
  cost := fun r => 2 * ((vec3 sx se sw).cost r + 1 + pcost (vx r) (ve r) (vw r)) + 2
  coefficient := 2 * ((vec3 sx se sw).coefficient + 1 + cP) + 2
  degree := (vec3 sx se sw).degree + dP
  cost_le := by
    intro r
    have h1 := (vec3 sx se sw).cost_le r
    have h2 := hpc r
    have hs := one_le_small a r
    have p1 : (r.smallSize a) ^ (vec3 sx se sw).degree ≤ (r.smallSize a) ^ ((vec3 sx se sw).degree + dP) :=
      Nat.pow_le_pow_right hs (by omega)
    have p2 : (r.smallSize a) ^ dP ≤ (r.smallSize a) ^ ((vec3 sx se sw).degree + dP) :=
      Nat.pow_le_pow_right hs (by omega)
    have p0 : 1 ≤ (r.smallSize a) ^ ((vec3 sx se sw).degree + dP) := Nat.one_le_pow _ _ hs
    have q1 := Nat.mul_le_mul_left (vec3 sx se sw).coefficient p1
    have q2 := Nat.mul_le_mul_left cP p2
    have e : (2 * ((vec3 sx se sw).coefficient + 1 + cP) + 2) * (r.smallSize a) ^ ((vec3 sx se sw).degree + dP) =
        2 * ((vec3 sx se sw).coefficient * (r.smallSize a) ^ ((vec3 sx se sw).degree + dP)) +
        2 * (r.smallSize a) ^ ((vec3 sx se sw).degree + dP) +
        2 * (cP * (r.smallSize a) ^ ((vec3 sx se sw).degree + dP)) +
        2 * (r.smallSize a) ^ ((vec3 sx se sw).degree + dP) := by ring
    rw [e]
    omega
  run := by
    intro r
    obtain ⟨hx, he, hp, hw⟩ := hgood r
    obtain ⟨H', A', st, h0, h1⟩ := core_run sx se sw r hx he hp hw
    obtain ⟨k, hm⟩ := step_mask0 st (fun _ => true) (by intro i _; rfl)
    rw [heads_succ, inBank_succ _ (by omega)] at hm
    refine ⟨_, _, hm, ?_, ?_, ?_, ?_⟩
    · have hc : (⟨0, by omega⟩ : Fin (2 + (15 + (vec3 sx se sw).extra) + 1)) =
          Fin.castAdd 1 (⟨0, by omega⟩ : Fin (2 + (15 + (vec3 sx se sw).extra))) := rfl
      rw [hc, Fin.addCases_left, h0]
    · have hc : (⟨0, by omega⟩ : Fin (2 + (15 + (vec3 sx se sw).extra) + 1)) =
          Fin.castAdd 1 (⟨0, by omega⟩ : Fin (2 + (15 + (vec3 sx se sw).extra))) := rfl
      rw [hc, Fin.addCases_left]
      rfl
    · have hc : (⟨1, by omega⟩ : Fin (2 + (15 + (vec3 sx se sw).extra) + 1)) =
          Fin.castAdd 1 (⟨1, by omega⟩ : Fin (2 + (15 + (vec3 sx se sw).extra))) := rfl
      rw [hc, Fin.addCases_left, h1]
    · have hc : (⟨1, by omega⟩ : Fin (2 + (15 + (vec3 sx se sw).extra) + 1)) =
          Fin.castAdd 1 (⟨1, by omega⟩ : Fin (2 + (15 + (vec3 sx se sw).extra))) := rfl
      rw [hc, Fin.addCases_left]
      rfl

end Stage

end
end NearCubicWires.PacketsKeys.Pow


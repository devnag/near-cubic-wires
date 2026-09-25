import Proof.Packets.PacketsGate
import Proof.Packets.PacketsLowerAdapter
import Proof.Packets.PacketsSeedDrivers
import Proof.Packets.PacketsVecAppend

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketFamilyParent
open NearCubicWires.PacketsConstruction NearCubicWires.PacketsConstruction.Residual
open NearCubicWires.PacketsGlue.RequestMeta
noncomputable section

/-! ## `1^C, 1^w ↦ 1^R` -/

namespace Reserve

/-- Template of `C`: `0 ↦ 0`, `1 ↦ 3`, `2 ↦ 5`. -/
def tcSlot (j : Fin (2 + 1)) : Fin (3 + 49) := ⟨if j.val = 0 then 0 else if j.val = 1 then 3 else 5, by split_ifs <;> omega⟩
/-- Template of `w`: `0 ↦ 1`, `1 ↦ 4`, `2 ↦ 6`. -/
def twSlot (j : Fin (2 + 1)) : Fin (3 + 49) := ⟨if j.val = 0 then 1 else if j.val = 1 then 4 else 6, by split_ifs <;> omega⟩
/-- The generator: `0 ↦ 3`, `1 ↦ 4`, `44 ↦ 2`, the rest from `7`. -/
def crSlot (j : Fin 48) : Fin (3 + 49) :=
  ⟨if j.val = 0 then 3 else if j.val = 1 then 4 else if j.val = 44 then 2 else if j.val < 44 then j.val + 5
    else j.val + 4, by have := j.isLt; split_ifs <;> omega⟩

theorem tcSlot_val (j : Fin (2 + 1)) : (tcSlot j).val = if j.val = 0 then 0 else if j.val = 1 then 3 else 5 := rfl
theorem twSlot_val (j : Fin (2 + 1)) : (twSlot j).val = if j.val = 0 then 1 else if j.val = 1 then 4 else 6 := rfl
theorem crSlot_val (j : Fin 48) : (crSlot j).val = if j.val = 0 then 3 else if j.val = 1 then 4 else if j.val = 44 then 2
    else if j.val < 44 then j.val + 5 else j.val + 4 := rfl

theorem tc_inj : Function.Injective tcSlot := by
  intro i j h; have hv := congrArg Fin.val h; rw [tcSlot_val, tcSlot_val] at hv
  have := i.isLt; have := j.isLt; apply Fin.ext; split_ifs at hv <;> omega
theorem tw_inj : Function.Injective twSlot := by
  intro i j h; have hv := congrArg Fin.val h; rw [twSlot_val, twSlot_val] at hv
  have := i.isLt; have := j.isLt; apply Fin.ext; split_ifs at hv <;> omega
theorem cr_inj : Function.Injective crSlot := by
  intro i j h; have hv := congrArg Fin.val h; rw [crSlot_val, crSlot_val] at hv
  apply Fin.ext; split_ifs at hv <;> omega

def machine :=
  Composition.machine (RecoveryFocus.machine tcSlot tplMap.machine)
    (Composition.machine (RecoveryFocus.machine twSlot tplMap.machine)
      (RecoveryFocus.machine crSlot Theorem25Completion.CycleCommonReserve.machine))

def cost (C w : ℕ) : ℕ := tplMap.cost C + 1 + (tplMap.cost w + 1 + Theorem25Completion.CycleCommonReserve.budget C w)

theorem run (C w : ℕ) : ∃ (H' : Fin (3 + 49) → ℕ) (A' : Fin (3 + 49) → List Bool),
    Step machine (cost C w) (fun _ => 0) (unIn2 (3 + 49) C w) H' A' ∧
    A' ⟨2, by omega⟩ = List.replicate (Theorem25Completion.CycleCommonReserve.reserve C w) true ∧
    H' ⟨2, by omega⟩ = 0 := by
  have hx : tplMap.extra = 1 := rfl
  obtain ⟨H1, A1, s1, a1, h1⟩ := tplMap.run C
  obtain ⟨HA, AA, st1, hs1, ho1⟩ := Dock.lift s1 tcSlot tc_inj (fun _ => 0) (fun _ => 0) (unIn2 (3 + 49) C w) (by
    intro j
    refine ⟨rfl, ?_⟩
    rw [ZeroPadding.pad_zero]
    have hj := j.isLt
    rcases (show j.val = 0 ∨ j.val = 1 ∨ j.val = 2 by omega) with h | h | h
    · have e : tcSlot j = ⟨0, by omega⟩ := Fin.ext (by rw [tcSlot_val]; simp [h])
      rw [e]; simp [unIn2, unIn, h]
    · have e : tcSlot j = ⟨3, by omega⟩ := Fin.ext (by rw [tcSlot_val]; simp [h])
      rw [e]; simp [unIn2, unIn, h]
    · have e : tcSlot j = ⟨5, by omega⟩ := Fin.ext (by rw [tcSlot_val]; simp [h])
      rw [e]; simp [unIn2, unIn, h])
  obtain ⟨H2, A2, s2, a2, h2⟩ := tplMap.run w
  have nA : ∀ i : Fin (3 + 49), i.val ≠ 0 → i.val ≠ 3 → i.val ≠ 5 → HA i = 0 ∧ AA i = unIn2 (3 + 49) C w i := by
    intro i h0 h3 h5
    apply ho1
    intro j hj; have hv := congrArg Fin.val hj; rw [tcSlot_val] at hv; split_ifs at hv <;> omega
  obtain ⟨HB, AB, st2, hs2, ho2⟩ := Dock.lift s2 twSlot tw_inj (fun _ => 0) HA AA (by
    intro j
    rw [ZeroPadding.pad_zero]
    have hj := j.isLt
    rcases (show j.val = 0 ∨ j.val = 1 ∨ j.val = 2 by omega) with h | h | h
    · have e : twSlot j = ⟨1, by omega⟩ := Fin.ext (by rw [twSlot_val]; simp [h])
      rw [e, (nA _ (by simp) (by simp) (by simp)).1, (nA _ (by simp) (by simp) (by simp)).2]
      simp [unIn2, unIn, h]
    · have e : twSlot j = ⟨4, by omega⟩ := Fin.ext (by rw [twSlot_val]; simp [h])
      rw [e, (nA _ (by simp) (by simp) (by simp)).1, (nA _ (by simp) (by simp) (by simp)).2]
      simp [unIn2, unIn, h]
    · have e : twSlot j = ⟨6, by omega⟩ := Fin.ext (by rw [twSlot_val]; simp [h])
      rw [e, (nA _ (by simp) (by simp) (by simp)).1, (nA _ (by simp) (by simp) (by simp)).2]
      simp [unIn2, unIn, h])
  have nB : ∀ i : Fin (3 + 49), i.val ≠ 1 → i.val ≠ 4 → i.val ≠ 6 → HB i = HA i ∧ AB i = AA i := by
    intro i h1' h4 h6
    apply ho2
    intro j hj; have hv := congrArg Fin.val hj; rw [twSlot_val] at hv; split_ifs at hv <;> omega
  have t3 : AB ⟨3, by omega⟩ = UnaryTemplate.tape C ∧ HB ⟨3, by omega⟩ = 0 := by
    rw [(nB _ (by simp) (by simp) (by simp)).1, (nB _ (by simp) (by simp) (by simp)).2]
    have e : (⟨3, by omega⟩ : Fin (3 + 49)) = tcSlot ⟨1, by omega⟩ := Fin.ext rfl
    rw [e, (hs1 _).1, (hs1 _).2, ZeroPadding.pad_zero]
    exact ⟨a1, h1⟩
  have t4 : AB ⟨4, by omega⟩ = UnaryTemplate.tape w ∧ HB ⟨4, by omega⟩ = 0 := by
    have e : (⟨4, by omega⟩ : Fin (3 + 49)) = twSlot ⟨1, by omega⟩ := Fin.ext rfl
    rw [e, (hs2 _).1, (hs2 _).2, ZeroPadding.pad_zero]
    exact ⟨a2, h2⟩
  have nAB : ∀ i : Fin (3 + 49), 7 ≤ i.val ∨ i.val = 2 → AB i = [] ∧ HB i = 0 := by
    intro i hi
    rw [(nB i (by omega) (by omega) (by omega)).1, (nB i (by omega) (by omega) (by omega)).2,
      (nA i (by omega) (by omega) (by omega)).1, (nA i (by omega) (by omega) (by omega)).2]
    simp only [unIn2]
    rw [if_neg (by omega), if_neg (by omega)]
    exact ⟨rfl, trivial⟩
  obtain ⟨HC, AC, st3, hs3, _⟩ := Dock.lift (Theorem25Completion.CycleCommonReserve.run C w) crSlot cr_inj
    (fun _ => 0) HB AB (by
      intro j
      rw [ZeroPadding.pad_zero]
      by_cases h0 : j.val = 0
      · have e : crSlot j = ⟨3, by omega⟩ := Fin.ext (by rw [crSlot_val]; simp [h0])
        rw [e, t3.1, t3.2]
        simp [Theorem25Completion.CycleCommonReserve.input, Fin.ext_iff, h0]
      by_cases h1' : j.val = 1
      · have e : crSlot j = ⟨4, by omega⟩ := Fin.ext (by rw [crSlot_val]; simp [h1'])
        rw [e, t4.1, t4.2]
        simp [Theorem25Completion.CycleCommonReserve.input, Fin.ext_iff, h1']
      · have hb := nAB (crSlot j) (by rw [crSlot_val]; have := j.isLt; split_ifs <;> omega)
        rw [hb.1, hb.2]
        refine ⟨rfl, ?_⟩
        simp only [Theorem25Completion.CycleCommonReserve.input]
        rw [if_neg (fun h => h0 (by simpa using congrArg Fin.val h)),
          if_neg (fun h => h1' (by simpa using congrArg Fin.val h))])
  refine ⟨HC, AC, st1.seq (st2.seq st3), ?_, ?_⟩
  · have e : (⟨2, by omega⟩ : Fin (3 + 49)) = crSlot 44 := Fin.ext rfl
    rw [e, (hs3 _).2, ZeroPadding.pad_zero, Theorem25Completion.CycleCommonReserve.raw_reserve]
  · have e : (⟨2, by omega⟩ : Fin (3 + 49)) = crSlot 44 := Fin.ext rfl
    rw [e, (hs3 _).1]

end Reserve

def reserveMap2 : UnaryMap2 Theorem25Completion.CycleCommonReserve.reserve where
  extra := 49
  states := _
  machine := Reserve.machine
  cost := Reserve.cost
  run := Reserve.run

/-! ## `1^R, 1^L ↦ 0^(R+1) 1 0^(L-R-2)` -/

namespace Term

/-- States: 0 walk the reserve writing `false`, 1 write the `true`, 2 fill `false` to the length, 3 halt.
Tapes: 0 `1^R`, 1 `1^L`, 2 the output. -/
def machine : Machine 3 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 3
  rule := fun q b =>
    if q.val = 0 then
      if b 0 then some ⟨0, fun i => if i.val = 2 then some false else none, fun _ => .right⟩
      else some ⟨1, fun i => if i.val = 2 then some false else none,
        fun i => if i.val = 0 then .stay else .right⟩
    else if q.val = 1 then
      some ⟨2, fun i => if i.val = 2 then some true else none, fun i => if i.val = 0 then .stay else .right⟩
    else if q.val = 2 then
      if b 1 then some ⟨2, fun i => if i.val = 2 then some false else none,
        fun i => if i.val = 0 then .stay else .right⟩
      else some ⟨3, fun _ => none, fun _ => .stay⟩
    else none

def cfg (R L : ℕ) (q : Fin 4) (h0 h1 : ℕ) (o : List Bool) : Configuration 3 4 :=
  ⟨q, ![h0, h1, o.length], ![List.replicate R true, List.replicate L true, o]⟩

theorem wr (o : List Bool) (b : Bool) : writeTapeBit o o.length b = o ++ [b] := Streaming.write_append o b

theorem wrr (n : ℕ) (b : Bool) : writeTapeBit (List.replicate n false) n b = List.replicate n false ++ [b] := by
  have h := wr (List.replicate n false) b
  rwa [List.length_replicate] at h

theorem stepA (R L i : ℕ) (hi : i < R) :
    step machine (cfg R L 0 i i (List.replicate i false)) =
      some (cfg R L 0 (i + 1) (i + 1) (List.replicate (i + 1) false)) := by
  have hr : readTapeBit (List.replicate R true) i = true := by simp [readTapeBit, List.getD, hi]
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]
    rw [wrr, List.replicate_succ']

theorem stepB (R L : ℕ) :
    step machine (cfg R L 0 R R (List.replicate R false)) =
      some (cfg R L 1 R (R + 1) (List.replicate (R + 1) false)) := by
  have hr : readTapeBit (List.replicate R true) R = false := by simp [readTapeBit, List.getD]
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]
    rw [wrr, List.replicate_succ']

theorem stepC (R L : ℕ) :
    step machine (cfg R L 1 R (R + 1) (List.replicate (R + 1) false)) =
      some (cfg R L 2 R (R + 2) (List.replicate (R + 1) false ++ [true])) := by
  simp only [step, machine, cfg, Configuration.scanned]
  simp
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]
    rw [wrr]

theorem stepD (R L p : ℕ) (o : List Bool) (hp : p < L) :
    step machine (cfg R L 2 R p o) = some (cfg R L 2 R (p + 1) (o ++ [false])) := by
  have hr : readTapeBit (List.replicate L true) p = true := by simp [readTapeBit, List.getD, hp]
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]
    rw [wr]

theorem stepE (R L p : ℕ) (o : List Bool) (hp : L ≤ p) :
    step machine (cfg R L 2 R p o) = some (cfg R L 3 R p o) := by
  have hr : readTapeBit (List.replicate L true) p = false := by simp [readTapeBit, List.getD, hp]
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  rfl

theorem walkA (R L m i : ℕ) (h : i + m = R) :
    Timed machine m (cfg R L 0 i i (List.replicate i false)) (cfg R L 0 R R (List.replicate R false)) := by
  induction m generalizing i with
  | zero =>
    have hi : i = R := by omega
    subst hi; exact Timed.refl _ _
  | succ m ih =>
    have e : m + 1 = 1 + m := by ring
    rw [e]
    exact (Timed.single (by rfl) (stepA R L i (by omega))).trans (ih (i + 1) (by omega))

theorem walkD (R L m p : ℕ) (o : List Bool) (h : p + m = max L p) :
    Timed machine (m + 1) (cfg R L 2 R p o) (cfg R L 3 R (max L p) (o ++ List.replicate m false)) := by
  induction m generalizing p o with
  | zero =>
    have hp : max L p = p := by omega
    rw [hp, List.replicate_zero, List.append_nil]
    exact Timed.single (by rfl) (stepE R L p o (by omega))
  | succ m ih =>
    have h2 := ih (p + 1) (o ++ [false]) (by omega)
    rw [show max L (p + 1) = max L p by omega, List.append_assoc, List.singleton_append, ← List.replicate_succ] at h2
    have e : m + 1 + 1 = 1 + (m + 1) := by ring
    rw [e]
    exact (Timed.single (by rfl) (stepD R L p o (by omega))).trans h2

/-- The terminal word. -/
def word (R L : ℕ) : List Bool := List.replicate (R + 1) false ++ true :: List.replicate (L - (R + 2)) false

theorem run (R L : ℕ) :
    Step machine (R + 3 + (L - (R + 2))) (fun _ => 0) ![List.replicate R true, List.replicate L true, []]
      ![R, max L (R + 2), (word R L).length] ![List.replicate R true, List.replicate L true, word R L] := by
  have h1 := walkA R L R 0 (by omega)
  have h2 := Timed.single (p := machine) (by rfl) (stepB R L)
  have h3 := Timed.single (p := machine) (by rfl) (stepC R L)
  have h4 := walkD R L (L - (R + 2)) (R + 2) (List.replicate (R + 1) false ++ [true]) (by omega)
  have ht := ((h1.trans h2).trans h3).trans h4
  have e : R + 1 + 1 + (L - (R + 2) + 1) = R + 3 + (L - (R + 2)) := by omega
  rw [e] at ht
  obtain ⟨r, hr, hf, _⟩ := ht.run (by rfl)
  have hc : cfg R L 0 0 0 (List.replicate 0 false) = (⟨machine.start, fun _ => 0,
      ![List.replicate R true, List.replicate L true, []]⟩ : Configuration 3 4) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hc] at hr
  have hw : List.replicate (R + 1) false ++ [true] ++ List.replicate (L - (R + 2)) false = word R L := by
    simp [word]
  refine Step.of_run hr ?_ ?_
  · rw [hf]; simp only [cfg, hw]
  · rw [hf]; simp only [cfg, hw]

end Term

theorem word2OfStep {s n x y : ℕ} {M : Machine 3 s} {hout : Fin 3 → ℕ} {z : List Bool}
    (h : Step M n (fun _ => 0) ![List.replicate x true, List.replicate y true, []] hout
      ![List.replicate x true, List.replicate y true, z]) :
    ∃ (H' : Fin (3 + 1) → ℕ) (A' : Fin (3 + 1) → List Bool),
      Step (MaskedReset.machine M (fun _ => true)) (2 * n + 2) (fun _ => 0) (unIn2 (3 + 1) x y) H' A' ∧
      A' ⟨2, by omega⟩ = z ∧ H' ⟨2, by omega⟩ = 0 := by
  obtain ⟨k, hm⟩ := readyMask h (fun _ => true) (fun _ _ => rfl)
  refine ⟨_, _, hm.congr_in ?_ ?_, rfl, rfl⟩
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.addCases_left]; fin_cases j <;> rfl
    · simp [unIn2]

def termMap : WordMap2 Term.word where
  extra := 1
  states := 4 + 2
  machine := MaskedReset.machine Term.machine (fun _ => true)
  cost := fun R L => 2 * (R + 3 + (L - (R + 2))) + 2
  run := fun R L => word2OfStep (Term.run R L)

theorem term_cost (x y : ℕ) : termMap.cost x y ≤ 4 * (x + y + 3) ^ 1 := by
  change 2 * (x + 3 + (y - (x + 2))) + 2 ≤ _
  rw [pow_one]; omega

/-! ## The stages (at the kit shape `kitShapePG a`) -/

section Stages
variable (a : DecompositionAlgorithm)

theorem reserve_pb : PB a (fun r => reserveMap2.cost (kitC a r) (wOf a r)) := by
  have hC : PB a (kitC a) := ⟨(kitShapePG a).cC, (kitShapePG a).dC, (kitShapePG a).C_le⟩
  have h2 : PB a (fun r => 2 ^ wOf a r) := ⟨(kitShapePG a).cW, (kitShapePG a).dW, (kitShapePG a).w_le⟩
  have hw : PB a (wOf a) := PB.mono h2 (fun r => (Nat.lt_two_pow_self).le)
  have hX : PB a (fun r => (kitC a r + wOf a r + 2) ^ 5) :=
    PB.pow (PB.add (PB.add hC hw (fun _ => le_refl _)) (PB.const 2) (fun _ => le_refl _)) 5 (fun _ => le_refl _)
  have hY : PB a (fun r => 2 ^ (8 * wOf a r)) :=
    PB.pow h2 8 (fun r => by rw [← pow_mul, Nat.mul_comm])
  have hB : PB a (fun r => 134217728 * (kitC a r + wOf a r + 2) ^ 5 * 2 ^ (8 * wOf a r)) :=
    PB.mul (PB.mul (PB.const _) hX (fun _ => le_refl _)) hY (fun _ => le_refl _)
  refine PB.add (PB.add (PB.mul (PB.const 2) hC (fun _ => le_refl _)) (PB.mul (PB.const 2) hw (fun _ => le_refl _))
    (fun _ => le_refl _)) (PB.add hB (PB.const 18) (fun _ => le_refl _)) (fun r => ?_)
  have hb := PacketsCombine.reserveGen_le (kitC a r) (wOf a r)
  change 2 * kitC a r + 8 + 1 + (2 * wOf a r + 8 + 1 + Theorem25Completion.CycleCommonReserve.budget (kitC a r) (wOf a r)) ≤ _
  omega

/-- The kit reserve `R = commonReserve C w` at the kit shape, in unary. -/
def reserveStage (wS : UnaryStage a (wOf a)) :
    UnaryStage a (fun r => Theorem25Completion.CycleCommonReserve.reserve (kitC a r) (wOf a r)) :=
  (kitCStage a).pair wS reserveMap2 (reserve_pb a).choose (reserve_pb a).choose_spec.choose
    (reserve_pb a).choose_spec.choose_spec

theorem reserve_eq (C w : ℕ) :
    Theorem25Completion.CycleCommonReserve.reserve C w = Theorem25Completion.CycleBounds.commonReserve C w := by
  unfold Theorem25Completion.CycleCommonReserve.reserve Theorem25Completion.CycleBounds.commonReserve
  rfl

def lenStage (wS : UnaryStage a (wOf a)) :
    UnaryStage a (fun r => ((r.family a).occurrences.length + 1) *
      (2 * Theorem25Completion.CycleBounds.commonReserve ((kitShapePG a).C r) ((kitShapePG a).w r))) :=
  (((popStage a).thenMapP (plusMap 1) 6 1 (plus_cost 1)).pairP
    ((reserveStage a wS).thenMapP (scaleMap 2) (4 * 2 + 12) 2 (scale_cost 2)) mulMap2 8 2 mul_cost).ofEq
    (fun r => by
      rw [reserve_eq, Nat.mul_comm _ 2]
      rfl)

/-- Transport a word stage along a pointwise equality of values. -/
def WordStage.congrW {v w : Request → List Bool} (s : WordStage a v) (h : ∀ r, v r = w r) : WordStage a w where
  extra := s.extra
  states := s.states
  machine := s.machine
  cost := s.cost
  coefficient := s.coefficient
  degree := s.degree
  cost_le := s.cost_le
  run := fun r => by
    obtain ⟨H', A', hs, h0, hh0, h1, hh1⟩ := s.run r
    exact ⟨H', A', hs, h0, hh0, h1.trans (h r), hh1⟩

theorem term_word (C w pop : ℕ) :
    Term.word (Theorem25Completion.CycleCommonReserve.reserve C w)
        ((pop + 1) * (2 * Theorem25Completion.CycleBounds.commonReserve C w)) =
      PolyKit.vector C w (ConeDegenerate.terminalVec pop) := by
  have hR : Theorem25Completion.CycleCommonReserve.reserve C w = PolyKit.reserve C w := by
    rw [reserve_eq]; rfl
  have hR' : Theorem25Completion.CycleBounds.commonReserve C w = PolyKit.reserve C w := rfl
  have h2 : 2 ≤ PolyKit.reserve C w := by
    rw [← hR]; unfold Theorem25Completion.CycleCommonReserve.reserve
    have h1 : 1 ≤ (C + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ 2 ^ (8 * w) := Nat.one_le_two_pow
    nlinarith
  have hC : C ≤ PolyKit.reserve C w := by
    rw [← hR]; unfold Theorem25Completion.CycleCommonReserve.reserve
    have h1 : C + 1 ≤ (C + 1) ^ 4 := Nat.le_self_pow (by decide) _
    have h2 : 1 ≤ 2 ^ (8 * w) := Nat.one_le_two_pow
    nlinarith
  rw [ConeDegenerate.vector_terminal C w pop hC (by omega), hR, hR']
  unfold Term.word
  congr 3
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- **DELIVERABLE: the terminal vector** (the `B = 0` branch's mask vector, request-level). -/
def termStage (wS : UnaryStage a (wOf a)) :
    WordStage a (fun r => PolyKit.vector ((kitShapePG a).C r) ((kitShapePG a).w r)
      (ConeDegenerate.terminalVec (r.family a).occurrences.length)) :=
  WordStage.congrW a ((reserveStage a wS).pairWP (lenStage a wS) termMap 4 1 term_cost)
    (fun r => term_word (kitC a r) (wOf a r) (r.family a).occurrences.length)

def nWordStage (walkS : UnaryStage a (walkLength a)) :
    WordStage a (fun r => RepairSource.VerifierDecoding.CompareMachine.word
      (2 * Nat.clog 2 (Request.denominator a r + 1))) :=
  WordStage.congrW a (stepsWordStage a walkS) (fun r => by rw [steps_eq])

end Stages

end
end NearCubicWires.PacketsSeed


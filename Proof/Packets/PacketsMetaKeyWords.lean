import Proof.Packets.PacketsCoordHoles
import Proof.Packets.PacketsKeysCoord
import Proof.Packets.PacketsMetaKeyDecode

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsMeta.Keys
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrime NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketFamilyParent
open NearCubicWires.PacketsConstruction NearCubicWires.PacketsConstruction.Residual
open NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.PacketsMeta.KeyDecode
noncomputable section

variable {a : DecompositionAlgorithm}

/-! ## Polynomial bounds in `smallSize` (local) -/

/-- `f` is bounded by a fixed power of `smallSize`. -/
def KB (a : DecompositionAlgorithm) (f : Request → ℕ) : Prop := ∃ c d : ℕ, ∀ r, f r ≤ c * (r.smallSize a) ^ d

def KB.c {f : Request → ℕ} (h : KB a f) : ℕ := Classical.choose h
def KB.d {f : Request → ℕ} (h : KB a f) : ℕ := Classical.choose (Classical.choose_spec h)
theorem KB.spec {f : Request → ℕ} (h : KB a f) (r : Request) : f r ≤ h.c * (r.smallSize a) ^ h.d :=
  Classical.choose_spec (Classical.choose_spec h) r

theorem KB.const (k : ℕ) : KB a (fun _ => k) := ⟨k, 0, fun r => by simp⟩

theorem KB.add {f g h : Request → ℕ} (hf : KB a f) (hg : KB a g) (e : ∀ r, h r ≤ f r + g r) : KB a h := by
  obtain ⟨c1, d1, h1⟩ := hf
  obtain ⟨c2, d2, h2⟩ := hg
  refine ⟨c1 + c2, d1 + d2, fun r => ?_⟩
  have hs := one_le_small a r
  have p1 : (r.smallSize a) ^ d1 ≤ (r.smallSize a) ^ (d1 + d2) := Nat.pow_le_pow_right hs (by omega)
  have p2 : (r.smallSize a) ^ d2 ≤ (r.smallSize a) ^ (d1 + d2) := Nat.pow_le_pow_right hs (by omega)
  have q1 := (h1 r).trans (Nat.mul_le_mul_left c1 p1)
  have q2 := (h2 r).trans (Nat.mul_le_mul_left c2 p2)
  have e2 := e r
  rw [Nat.add_mul]
  omega

theorem KB.mul {f g h : Request → ℕ} (hf : KB a f) (hg : KB a g) (e : ∀ r, h r ≤ f r * g r) : KB a h := by
  obtain ⟨c1, d1, h1⟩ := hf
  obtain ⟨c2, d2, h2⟩ := hg
  refine ⟨c1 * c2, d1 + d2, fun r => (e r).trans ?_⟩
  calc f r * g r ≤ (c1 * (r.smallSize a) ^ d1) * (c2 * (r.smallSize a) ^ d2) := Nat.mul_le_mul (h1 r) (h2 r)
    _ = c1 * c2 * (r.smallSize a) ^ (d1 + d2) := by rw [pow_add]; ring

theorem KB.pow {f h : Request → ℕ} (hf : KB a f) (k : ℕ) (e : ∀ r, h r ≤ f r ^ k) : KB a h := by
  obtain ⟨c, d, h1⟩ := hf
  refine ⟨c ^ k, d * k, fun r => (e r).trans ?_⟩
  calc f r ^ k ≤ (c * (r.smallSize a) ^ d) ^ k := Nat.pow_le_pow_left (h1 r) k
    _ = c ^ k * (r.smallSize a) ^ (d * k) := by rw [mul_pow, ← pow_mul]

theorem KB.ofStage {v : Request → ℕ} (s : UnaryStage a v) : KB a v :=
  ⟨s.coefficient + 7, s.degree + 1, fun r => by have := s.value_bound r; omega⟩

theorem KB.cost {v : ∀ r : Request, rcKey a r → List Bool} (s : KeyWord a v) : KB a s.cost :=
  ⟨s.costC, s.costD, s.cost_le⟩

/-- **The digit bound is a fixed power of `smallSize`.** -/
theorem digit_kb (a : DecompositionAlgorithm) : KB a (digitBound a) := by
  have hS : KB a (seedCount a) := ⟨8, 163, fun r => Seed.seedCount_le_small a r⟩
  have hC : KB a (coordSum a) := KB.ofStage (PacketsKeys.Native.coordStage a)
  have hT : KB a (cutoffOf a) := KB.ofStage (NearCubicWires.PacketsMeta.cutoffStage a)
  have h1 : KB a (fun r => seedCount a r + coordSum a r) := KB.add hS hC (fun r => le_refl _)
  have h2 : KB a (fun r => cutoffOf a r + (cutoffOf a r + 2)) :=
    KB.add hT (KB.add hT (KB.const 2) (fun r => le_refl _)) (fun r => le_refl _)
  refine KB.add h1 h2 (fun r => ?_)
  show digitBound a r ≤ seedCount a r + coordSum a r + (cutoffOf a r + (cutoffOf a r + 2))
  rw [digitBound_eq]
  have e1 : liveFlag r * seedCount a r ≤ seedCount a r := by
    have := liveFlag_le r
    rcases (show liveFlag r = 0 ∨ liveFlag r = 1 by omega) with h | h <;> simp [h]
  have e2 := pc_le (cutoffOf a r)
  omega

theorem width_le_bound (a : DecompositionAlgorithm) (r : Request) : PacketsConstruction.fieldWidth a r ≤ digitBound a r := by
  have h2 := two_le_bound a r
  have hp := Nat.pow_log_le_self 2 (show digitBound a r ≠ 0 by omega)
  have hl : Nat.log 2 (digitBound a r) < 2 ^ Nat.log 2 (digitBound a r) := Nat.lt_two_pow_self
  change Nat.log 2 (digitBound a r) + 1 ≤ digitBound a r
  omega

/-! ## `metaEntry` facts -/

theorem me_congr (r : Request) (c : Option (rcKey a r)) {t t' : ℕ} (i : Fin t) (j : Fin t') (h : i.val = j.val) :
    PacketsCombine.metaEntry a r c t i = PacketsCombine.metaEntry a r c t' j := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  simp only at h
  subst h
  rfl

theorem me_hi (r : Request) (c : Option (rcKey a r)) {t : ℕ} (i : Fin t) (h : 9 ≤ i.val) :
    PacketsCombine.metaEntry a r c t i = [] := by
  unfold PacketsCombine.metaEntry
  rw [if_neg (by omega), dif_neg (by omega)]

theorem me_field (r : Request) (c : Option (rcKey a r)) {t : ℕ} (f : Fin 8) (i : Fin t) (h : i.val = f.val + 1) :
    PacketsCombine.metaEntry a r c t i = RepairOrdinary.frame (SignedSortKey.binary (PacketsConstruction.fieldWidth a r) (keyDigits a r c f)) := by
  unfold PacketsCombine.metaEntry PacketsCombine.keyWord
  rw [if_neg (by omega), dif_pos (show 1 ≤ i.val ∧ i.val ≤ 8 by have := f.isLt; omega)]
  exact congrArg (fun x => RepairOrdinary.frame (SignedSortKey.binary (PacketsConstruction.fieldWidth a r) (keyDigits a r c x)))
    (Fin.ext (by show i.val - 1 = f.val; omega))

/-! ## One key field in unary -/

section Field
variable (a) (f : Fin 8)

def fkS (j : Fin (9 + 1)) : Fin (10 + 8) :=
  ⟨if j.val = 0 then f.val + 1 else if j.val = 1 then 9 else j.val + 8, by
    have := j.isLt; have := f.isLt; split_ifs <;> omega⟩

theorem fkS_val (j : Fin (9 + 1)) :
    (fkS f j).val = if j.val = 0 then f.val + 1 else if j.val = 1 then 9 else j.val + 8 := rfl

theorem fkS_inj : Function.Injective (fkS f) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [fkS_val, fkS_val] at hv
  have := f.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

def fieldCost (r : Request) : ℕ := decCost (PacketsConstruction.fieldWidth a r) (digitBound a r)

theorem decCost_le (W B : ℕ) : decCost W B ≤ 100 * (W + B + 1) ^ 2 := by
  unfold decCost pCost emitCost PacketsKeys.Setup.cost
  nlinarith [Nat.zero_le W, Nat.zero_le B]

theorem fieldCost_kb : KB a (fieldCost a) := by
  have hB := digit_kb a
  have h1 : KB a (fun r => digitBound a r + (digitBound a r + 1)) :=
    KB.add hB (KB.add hB (KB.const 1) (fun r => le_refl _)) (fun r => le_refl _)
  have h2 : KB a (fun r => (digitBound a r + (digitBound a r + 1)) ^ 2) := KB.pow h1 2 (fun r => le_refl _)
  refine KB.mul (KB.const 100) h2 (fun r => ?_)
  show fieldCost a r ≤ 100 * (digitBound a r + (digitBound a r + 1)) ^ 2
  have e1 := decCost_le (PacketsConstruction.fieldWidth a r) (digitBound a r)
  have e2 := width_le_bound a r
  have e3 : (PacketsConstruction.fieldWidth a r + digitBound a r + 1) ^ 2 ≤ (digitBound a r + (digitBound a r + 1)) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  unfold fieldCost
  calc decCost (PacketsConstruction.fieldWidth a r) (digitBound a r)
      ≤ 100 * (PacketsConstruction.fieldWidth a r + digitBound a r + 1) ^ 2 := e1
    _ ≤ 100 * (digitBound a r + (digitBound a r + 1)) ^ 2 := Nat.mul_le_mul_left _ e3

/-- **Key field `f` in unary** (one fixed machine: the digit decoder on tape `f + 1`, output on tape 9). -/
def fieldKey : KeyWord a (fun r k => List.replicate (keyDigits a r (some k) f) true) where
  extra := 8
  states := _
  machine := RecoveryFocus.machine (fkS f) decM
  cost := fieldCost a
  costC := (fieldCost_kb a).c
  costD := (fieldCost_kb a).d
  cost_le := (fieldCost_kb a).spec
  run := fun r k hk => by
    have hc : CodeValid a r (some k) := Or.inr ⟨k, hk, rfl⟩
    have hd := digit_lt_pow a r (some k) hc f
    have hdB := (digit_lt_bound a r (some k) hc f).le
    obtain ⟨H', A', st, hA0, hH0, hA1, hH1⟩ := dec_run (PacketsConstruction.fieldWidth a r) (keyDigits a r (some k) f)
      (digitBound a r) hd hdB
    obtain ⟨H, A, st', hs, ho⟩ := NearCubicWires.PacketsConstruction.Dock.lift st (fkS f) (fkS_inj f)
      (fun _ => 0) (fun _ => 0) (PacketsCombine.metaEntry a r (some k) (10 + 8)) (by
        intro j
        refine ⟨rfl, ?_⟩
        rw [ZeroPadding.pad_zero]
        by_cases h0 : j.val = 0
        · rw [me_field r (some k) f _ (by rw [fkS_val]; simp [h0])]
          simp [decIn, h0]
        · rw [me_hi r (some k) _ (by rw [fkS_val]; split_ifs <;> omega)]
          simp [decIn, h0])
    refine ⟨H, A, st', ?_, ?_, ?_⟩
    · intro i hi
      by_cases hf : i.val = f.val + 1
      · have e : i = fkS f ⟨0, by omega⟩ := Fin.ext (by rw [fkS_val]; simp; omega)
        rw [e, (hs _).1, (hs _).2, ZeroPadding.pad_zero, hA0]
        exact ⟨(me_field r (some k) f (fkS f ⟨0, by omega⟩) (by rw [fkS_val]; simp)).symm, hH0⟩
      · have hn : ∀ j, fkS f j ≠ i := by
          intro j hj
          have hv := congrArg Fin.val hj
          rw [fkS_val] at hv
          split_ifs at hv <;> omega
        exact ⟨(ho i hn).2, (ho i hn).1⟩
    · have e : (⟨9, by omega⟩ : Fin (10 + 8)) = fkS f ⟨1, by omega⟩ := Fin.ext (by rw [fkS_val]; simp)
      rw [e, (hs _).2, ZeroPadding.pad_zero]
      exact hA1
    · have e : (⟨9, by omega⟩ : Fin (10 + 8)) = fkS f ⟨1, by omega⟩ := Fin.ext (by rw [fkS_val]; simp)
      rw [e, (hs _).1]
      exact hH1

end Field

/-! ## Two key words through a two-argument unary map (generic) -/

/-- A key word docked by a slot map that fixes the low tapes 0–8: frame form. -/
theorem kw_dock {v : ∀ r : Request, rcKey a r → List Bool} (s : KeyWord a v) {u : ℕ}
    (σ : Fin (10 + s.extra) → Fin u) (hσ : Function.Injective σ)
    (r : Request) (k : rcKey a r) (hk : k ∈ rcKeys a r) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hin : ∀ j, H (σ j) = 0 ∧ A (σ j) = PacketsCombine.metaEntry a r (some k) (10 + s.extra) j) :
    ∃ (H' : Fin u → ℕ) (A' : Fin u → List Bool), Step (RecoveryFocus.machine σ s.machine) (s.cost r) H A H' A' ∧
      (∀ j : Fin (10 + s.extra), j.val < 9 →
        H' (σ j) = 0 ∧ A' (σ j) = PacketsCombine.metaEntry a r (some k) (10 + s.extra) j) ∧
      H' (σ ⟨9, by omega⟩) = 0 ∧ A' (σ ⟨9, by omega⟩) = v r k ∧
      (∀ i, (∀ j, σ j ≠ i) → H' i = H i ∧ A' i = A i) := by
  obtain ⟨H1, A1, st, hkeep, h9, h9H⟩ := s.run r k hk
  obtain ⟨H', A', st', hs, ho⟩ := NearCubicWires.PacketsConstruction.Dock.lift st σ hσ (fun _ => 0) H A (by
    intro j; rw [ZeroPadding.pad_zero]; exact ⟨(hin j).1, (hin j).2⟩)
  refine ⟨H', A', st', fun j hj => ?_, ?_, ?_, ho⟩
  · rw [(hs j).1, (hs j).2, ZeroPadding.pad_zero]
    exact ⟨(hkeep j hj).2, (hkeep j hj).1⟩
  · rw [(hs _).1]; exact h9H
  · rw [(hs _).2, ZeroPadding.pad_zero]; exact h9

section Pair
variable {v1 v2 : ∀ r : Request, rcKey a r → ℕ} {g : ℕ → ℕ → ℕ}
variable (s1 : KeyWord a (fun r k => List.replicate (v1 r k) true))
variable (s2 : KeyWord a (fun r k => List.replicate (v2 r k) true))
variable (m : UnaryMap2 g)

def pE : ℕ := 2 + s1.extra + s2.extra + m.extra

def pS1 (j : Fin (10 + s1.extra)) : Fin (10 + pE s1 s2 m) :=
  ⟨if j.val < 9 then j.val else if j.val = 9 then 10 else j.val + 2, by
    have := j.isLt; unfold pE; split_ifs <;> omega⟩
def pS2 (j : Fin (10 + s2.extra)) : Fin (10 + pE s1 s2 m) :=
  ⟨if j.val < 9 then j.val else if j.val = 9 then 11 else j.val + 2 + s1.extra, by
    have := j.isLt; unfold pE; split_ifs <;> omega⟩
def pS3 (j : Fin (3 + m.extra)) : Fin (10 + pE s1 s2 m) :=
  ⟨if j.val = 0 then 10 else if j.val = 1 then 11 else if j.val = 2 then 9 else j.val + 9 + s1.extra + s2.extra, by
    have := j.isLt; unfold pE; split_ifs <;> omega⟩

theorem pS1_val (j : Fin (10 + s1.extra)) :
    (pS1 s1 s2 m j).val = if j.val < 9 then j.val else if j.val = 9 then 10 else j.val + 2 := rfl
theorem pS2_val (j : Fin (10 + s2.extra)) :
    (pS2 s1 s2 m j).val = if j.val < 9 then j.val else if j.val = 9 then 11 else j.val + 2 + s1.extra := rfl
theorem pS3_val (j : Fin (3 + m.extra)) :
    (pS3 s1 s2 m j).val =
      if j.val = 0 then 10 else if j.val = 1 then 11 else if j.val = 2 then 9 else j.val + 9 + s1.extra + s2.extra := rfl

theorem pS1_inj : Function.Injective (pS1 s1 s2 m) := by
  intro i j h; have hv := congrArg Fin.val h; rw [pS1_val, pS1_val] at hv; apply Fin.ext; split_ifs at hv <;> omega
theorem pS2_inj : Function.Injective (pS2 s1 s2 m) := by
  intro i j h; have hv := congrArg Fin.val h; rw [pS2_val, pS2_val] at hv; apply Fin.ext; split_ifs at hv <;> omega
theorem pS3_inj : Function.Injective (pS3 s1 s2 m) := by
  intro i j h; have hv := congrArg Fin.val h; rw [pS3_val, pS3_val] at hv; apply Fin.ext; split_ifs at hv <;> omega

def pairMachine :=
  Composition.machine (RecoveryFocus.machine (pS1 s1 s2 m) s1.machine)
    (Composition.machine (RecoveryFocus.machine (pS2 s1 s2 m) s2.machine) (RecoveryFocus.machine (pS3 s1 s2 m) m.machine))

def pairCost (mb : Request → ℕ) (r : Request) : ℕ := s1.cost r + 1 + (s2.cost r + 1 + mb r)

theorem pairCost_kb (mb : Request → ℕ) (hmk : KB a mb) : KB a (pairCost s1 s2 mb) := by
  have h3 : KB a (fun r => s2.cost r + 1 + mb r) :=
    KB.add (KB.add (KB.cost s2) (KB.const 1) (fun r => le_refl _)) hmk (fun r => le_refl _)
  have h4 : KB a (fun r => s1.cost r + 1 + (s2.cost r + 1 + mb r)) :=
    KB.add (KB.add (KB.cost s1) (KB.const 1) (fun r => le_refl _)) h3 (fun r => le_refl _)
  exact h4

theorem pair_run (mb : Request → ℕ) (hmb : ∀ r k, k ∈ rcKeys a r → m.cost (v1 r k) (v2 r k) ≤ mb r)
    (r : Request) (k : rcKey a r) (hk : k ∈ rcKeys a r) :
    ∃ (H : Fin (10 + pE s1 s2 m) → ℕ) (A : Fin (10 + pE s1 s2 m) → List Bool),
      Step (pairMachine s1 s2 m) (pairCost s1 s2 mb r) (fun _ => 0)
        (PacketsCombine.metaEntry a r (some k) (10 + pE s1 s2 m)) H A ∧
      (∀ i : Fin (10 + pE s1 s2 m), i.val < 9 →
        A i = PacketsCombine.metaEntry a r (some k) (10 + pE s1 s2 m) i ∧ H i = 0) ∧
      A ⟨9, by omega⟩ = List.replicate (g (v1 r k) (v2 r k)) true ∧ H ⟨9, by omega⟩ = 0 := by
  -- stage 1: `s1`, output on tape 10
  obtain ⟨H1, A1, st1, lo1, h91, a91, ot1⟩ := kw_dock s1 (pS1 s1 s2 m) (pS1_inj s1 s2 m) r k hk (fun _ => 0)
    (PacketsCombine.metaEntry a r (some k) (10 + pE s1 s2 m)) (by
      intro j
      refine ⟨rfl, ?_⟩
      by_cases hj : j.val < 9
      · exact me_congr r (some k) _ _ (by rw [pS1_val]; simp [hj])
      · rw [me_hi r (some k) _ (by rw [pS1_val]; split_ifs <;> omega), me_hi r (some k) _ (by omega)])
  -- stage 2: `s2`, output on tape 11
  obtain ⟨H2, A2, st2, lo2, h92, a92, ot2⟩ := kw_dock s2 (pS2 s1 s2 m) (pS2_inj s1 s2 m) r k hk H1 A1 (by
    intro j
    by_cases hj : j.val < 9
    · have e : pS2 s1 s2 m j = pS1 s1 s2 m ⟨j.val, by omega⟩ := Fin.ext (by rw [pS2_val, pS1_val]; simp [hj])
      rw [e]
      obtain ⟨x1, x2⟩ := lo1 ⟨j.val, by omega⟩ hj
      exact ⟨x1, x2.trans (me_congr r (some k) _ _ rfl)⟩
    · have hn : ∀ j', pS1 s1 s2 m j' ≠ pS2 s1 s2 m j := by
        intro j' hj'
        have hv := congrArg Fin.val hj'
        rw [pS1_val, pS2_val] at hv
        have := j'.isLt
        have := j.isLt
        split_ifs at hv <;> omega
      obtain ⟨x1, x2⟩ := ot1 _ hn
      refine ⟨x1, x2.trans ?_⟩
      rw [me_hi r (some k) _ (by rw [pS2_val]; split_ifs <;> omega), me_hi r (some k) _ (by omega)])
  -- stage 3: the map, output on tape 9
  obtain ⟨H', A', mst, hA2, hH2⟩ := m.run (v1 r k) (v2 r k)
  have n1 : ∀ j', pS2 s1 s2 m j' ≠ pS1 s1 s2 m ⟨9, by omega⟩ := by
    intro j' hj'
    have hv := congrArg Fin.val hj'
    have h9 : (pS1 s1 s2 m ⟨9, by omega⟩).val = 10 := by rw [pS1_val]; simp
    rw [h9, pS2_val] at hv
    have := j'.isLt
    split_ifs at hv <;> omega
  obtain ⟨H3, A3, st3, hs3, ho3⟩ := NearCubicWires.PacketsConstruction.Dock.lift (mst.enlarge (hmb r k hk))
    (pS3 s1 s2 m) (pS3_inj s1 s2 m) (fun _ => 0) H2 A2 (by
      intro j
      rw [ZeroPadding.pad_zero]
      by_cases j0 : j.val = 0
      · have e : pS3 s1 s2 m j = pS1 s1 s2 m ⟨9, by omega⟩ := Fin.ext (by rw [pS3_val, pS1_val]; simp [j0])
        rw [e, (ot2 _ n1).1, (ot2 _ n1).2, h91, a91]
        simp [unIn2, j0]
      by_cases j1 : j.val = 1
      · have e : pS3 s1 s2 m j = pS2 s1 s2 m ⟨9, by omega⟩ := Fin.ext (by rw [pS3_val, pS2_val]; simp [j1])
        rw [e, h92, a92]
        simp [unIn2, j1]
      · have hn2 : ∀ j', pS2 s1 s2 m j' ≠ pS3 s1 s2 m j := by
          intro j' hj'
          have hv := congrArg Fin.val hj'
          rw [pS2_val, pS3_val] at hv
          have := j'.isLt
          have := j.isLt
          split_ifs at hv <;> omega
        have hn1 : ∀ j', pS1 s1 s2 m j' ≠ pS3 s1 s2 m j := by
          intro j' hj'
          have hv := congrArg Fin.val hj'
          rw [pS1_val, pS3_val] at hv
          have := j'.isLt
          have := j.isLt
          split_ifs at hv <;> omega
        rw [(ot2 _ hn2).1, (ot2 _ hn2).2, (ot1 _ hn1).1, (ot1 _ hn1).2,
          me_hi r (some k) _ (by rw [pS3_val]; split_ifs <;> omega)]
        simp [unIn2, j0, j1])
  refine ⟨H3, A3, st1.seq (st2.seq st3), ?_, ?_, ?_⟩
  · intro i hi
    have hn3 : ∀ j, pS3 s1 s2 m j ≠ i := by
      intro j hj
      have hv := congrArg Fin.val hj
      rw [pS3_val] at hv
      split_ifs at hv <;> omega
    have e : i = pS2 s1 s2 m ⟨i.val, by omega⟩ := Fin.ext (by rw [pS2_val]; simp [hi])
    rw [(ho3 i hn3).1, (ho3 i hn3).2]
    rw [e]
    obtain ⟨x1, x2⟩ := lo2 ⟨i.val, by omega⟩ hi
    refine ⟨x2.trans (me_congr r (some k) _ _ ?_), x1⟩
    rw [pS2_val]; simp [hi]
  · have e : (⟨9, by omega⟩ : Fin (10 + pE s1 s2 m)) = pS3 s1 s2 m ⟨2, by omega⟩ := Fin.ext (by rw [pS3_val]; simp)
    rw [e, (hs3 _).2, ZeroPadding.pad_zero]
    exact hA2
  · have e : (⟨9, by omega⟩ : Fin (10 + pE s1 s2 m)) = pS3 s1 s2 m ⟨2, by omega⟩ := Fin.ext (by rw [pS3_val]; simp)
    rw [e, (hs3 _).1]
    exact hH2

end Pair

/-- **Two key words through a two-argument unary map** (one fixed machine). -/
def KeyWord.pair {v1 v2 : ∀ r : Request, rcKey a r → ℕ} {g : ℕ → ℕ → ℕ}
    (s1 : KeyWord a (fun r k => List.replicate (v1 r k) true)) (s2 : KeyWord a (fun r k => List.replicate (v2 r k) true))
    (m : UnaryMap2 g) (mb : Request → ℕ) (hmb : ∀ r k, k ∈ rcKeys a r → m.cost (v1 r k) (v2 r k) ≤ mb r)
    (hmk : KB a mb) : KeyWord a (fun r k => List.replicate (g (v1 r k) (v2 r k)) true) where
  extra := pE s1 s2 m
  states := _
  machine := pairMachine s1 s2 m
  cost := pairCost s1 s2 mb
  costC := (pairCost_kb s1 s2 mb hmk).c
  costD := (pairCost_kb s1 s2 mb hmk).d
  cost_le := (pairCost_kb s1 s2 mb hmk).spec
  run := fun r k hk => pair_run s1 s2 m mb hmb r k hk

/-! ## The two THR key decodings -/

section Decodings
variable (a)

def cutKey : KeyWord a (fun r _ => List.replicate (cutoffOf a r) true) :=
  KeyWord.ofWord (NearCubicWires.PacketsMeta.cutoffStage a).toWord

/-- The prime service's uniform fuel over the keys of a request. -/
def primeMb (r : Request) : ℕ := 14 * (cutoffOf a r + digitBound a r + 3) ^ 3

theorem primeMb_kb : KB a (primeMb a) := by
  have hT : KB a (cutoffOf a) := KB.ofStage (NearCubicWires.PacketsMeta.cutoffStage a)
  have h1 : KB a (fun r => cutoffOf a r + digitBound a r + 3) :=
    KB.add (KB.add hT (digit_kb a) (fun r => le_refl _)) (KB.const 3) (fun r => le_refl _)
  exact KB.mul (KB.const 14) (KB.pow h1 3 (fun r => le_refl _)) (fun r => le_refl _)

theorem primeMb_le (r : Request) (k : rcKey a r) (hk : k ∈ rcKeys a r) :
    primeOfIndexMap.cost (cutoffOf a r) (keyDigits a r (some k) 4) ≤ primeMb a r := by
  have h1 := primeIdx_cost (cutoffOf a r) (keyDigits a r (some k) 4)
  have h2 := digit_lt_bound a r (some k) (Or.inr ⟨k, hk, rfl⟩) 4
  have h3 : (cutoffOf a r + keyDigits a r (some k) 4 + 3) ^ 3 ≤ (cutoffOf a r + digitBound a r + 3) ^ 3 :=
    Nat.pow_le_pow_left (by omega) 3
  unfold primeMb
  omega

/-- **`primeW`**: the prime VALUE of a key, in unary (key field 4 = the prime's index among the primes up to the
cutoff, mapped by PG's `primeOfIndexMap`). -/
def primeW : KeyWord a (fun r k => List.replicate (PacketsGlue.primeAt (cutoffOf a r) (keyDigits a r (some k) 4)) true) :=
  KeyWord.pair (v1 := fun r _ => cutoffOf a r) (v2 := fun r k => keyDigits a r (some k) 4) (cutKey a) (fieldKey a 4)
    primeOfIndexMap (primeMb a) (primeMb_le a) (primeMb_kb a)

/-- **`resW`**: the residue of a key, in unary (key field 6). -/
def resW : KeyWord a (fun r k => List.replicate (keyDigits a r (some k) 6) true) := fieldKey a 6

theorem primeAt_idx (c : ℕ) (x : PrimeIndex c) : PacketsGlue.primeAt c (primeIndexFinEquiv c x).val = x.val := by
  unfold PacketsGlue.primeAt
  rw [dif_pos (primeIndexFinEquiv c x).isLt]
  simp

theorem primeW_thr (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target) :
    List.replicate (PacketsGlue.primeAt (cutoffOf a (.thr r four L target))
      (keyDigits a (.thr r four L target) (some k) 4)) true = List.replicate k.prime.val true := by
  have h4 : keyDigits a (.thr r four L target) (some k) 4 = (primeIndexFinEquiv _ k.prime).val := by
    rw [keyDigits_thr, dif_neg (show ¬ ((4 : Fin 8).val < r.circuits.length) from fun h => by
      change 4 < _ at h; omega), if_pos (show (4 : Fin 8).val = 4 from rfl)]
  rw [h4]
  exact congrArg (fun n => List.replicate n true) (primeAt_idx _ k.prime)

theorem resW_thr (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target) :
    List.replicate (keyDigits a (.thr r four L target) (some k) 6) true = List.replicate k.residue.val true := by
  rw [keyDigits_thr, dif_neg (show ¬ ((6 : Fin 8).val < r.circuits.length) from fun h => by
      change 6 < _ at h; omega), if_neg (show ¬ ((6 : Fin 8).val = 4) from by decide),
    if_neg (show ¬ ((6 : Fin 8).val = 5) from by decide), if_pos (show (6 : Fin 8).val = 6 from rfl)]

end Decodings

end
end NearCubicWires.PacketsMeta.Keys


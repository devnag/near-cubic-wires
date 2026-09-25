import Proof.Packets.PacketsCombineSymRun

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open NearCubicWires.PacketsConstruction
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
noncomputable section

section Local
variable (e Rb : ℕ) (input : List Bool) (keys : Fin 8 → List Bool) (coords : List Bool)

/-- The local entry: input, key words, the coordinate bank (padded), all else blank. -/
def lentry (i : Fin (117 + e)) : List Bool :=
  if i.val = 0 then input
  else if h : 1 ≤ i.val ∧ i.val ≤ 8 then keys ⟨i.val - 1, by omega⟩
  else if i.val = 9 then ZeroPadding.pad Rb coords else ZeroPadding.pad Rb []

/-- The metadata machine's exact entry (generic `metaEntry`). -/
def metaIn (i : Fin (16 + e)) : List Bool :=
  if i.val = 0 then input else if h : 1 ≤ i.val ∧ i.val ≤ 8 then keys ⟨i.val - 1, by omega⟩ else []

theorem lentry_high (i : Fin (117 + e)) (h : 10 ≤ i.val) :
    lentry e Rb input keys coords i = ZeroPadding.pad Rb [] := by
  unfold lentry
  rw [if_neg (by omega), dif_neg (by omega), if_neg (by omega)]

theorem lentry_meta (j : Fin (16 + e)) (hj : j.val ≤ 8) :
    lentry e Rb input keys coords (metaSlot e j) = metaIn e input keys j := by
  have hv : (metaSlot e j).val = j.val := by simp [metaSlot, metaSlotVal, hj]
  unfold lentry metaIn
  simp only [hv]
  split_ifs <;> first | rfl | omega

end Local

/-! ## Stage 1: the metadata -/

section Stage1
variable (e Rb C w m n : ℕ) (input : List Bool) (keys : Fin 8 → List Bool) (coords bits : List Bool)

def Facts1 (H : Fin (117 + e) → ℕ) (A : Fin (117 + e) → List Bool) : Prop :=
  (∀ i : Fin (117 + e), i.val ≤ 9 → A i = lentry e Rb input keys coords i ∧ H i = 0) ∧
  (∀ i : Fin (117 + e), 18 ≤ i.val → i.val < 117 → A i = ZeroPadding.pad Rb [] ∧ H i = 0) ∧
  A ⟨10, by omega⟩ = ZeroPadding.pad Rb [] ∧ H ⟨10, by omega⟩ = 0 ∧
  A ⟨11, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape C) ∧ H ⟨11, by omega⟩ = 0 ∧
  A ⟨12, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape C) ∧ H ⟨12, by omega⟩ = 0 ∧
  A ⟨13, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape w) ∧ H ⟨13, by omega⟩ = 0 ∧
  A ⟨14, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape m) ∧ H ⟨14, by omega⟩ = 0 ∧
  A ⟨15, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape n) ∧ H ⟨15, by omega⟩ = 0 ∧
  A ⟨16, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape (n * m)) ∧ H ⟨16, by omega⟩ = 0 ∧
  A ⟨17, by omega⟩ = ZeroPadding.pad Rb bits ∧ H ⟨17, by omega⟩ = n * m

theorem stage1 {s : ℕ} (M : Machine (16 + e) s) (mcost : ℕ) (mH : Fin (16 + e) → ℕ)
    (mA : Fin (16 + e) → List Bool)
    (hm : Step M mcost (fun _ => 0) (metaIn e input keys) mH mA)
    (hk : ∀ i : Fin (16 + e), i.val ≤ 8 → mA i = metaIn e input keys i ∧ mH i = 0)
    (h9 : mA ⟨9, by omega⟩ = UnaryTemplate.tape C ∧ mH ⟨9, by omega⟩ = 0)
    (h10 : mA ⟨10, by omega⟩ = UnaryTemplate.tape C ∧ mH ⟨10, by omega⟩ = 0)
    (h11 : mA ⟨11, by omega⟩ = UnaryTemplate.tape w ∧ mH ⟨11, by omega⟩ = 0)
    (h12 : mA ⟨12, by omega⟩ = UnaryTemplate.tape m ∧ mH ⟨12, by omega⟩ = 0)
    (h13 : mA ⟨13, by omega⟩ = UnaryTemplate.tape n ∧ mH ⟨13, by omega⟩ = 0)
    (h14 : mA ⟨14, by omega⟩ = UnaryTemplate.tape (n * m) ∧ mH ⟨14, by omega⟩ = 0)
    (h15 : mA ⟨15, by omega⟩ = bits ∧ mH ⟨15, by omega⟩ = n * m) :
    ∃ (H : Fin (117 + e) → ℕ) (A : Fin (117 + e) → List Bool),
      Step (RecoveryFocus.machine (metaSlot e) M) mcost (fun _ => 0) (lentry e Rb input keys coords) H A ∧
      Facts1 e Rb C w m n input keys coords bits H A := by
  obtain ⟨H, A, st, o, kp⟩ := Dock.lift hm (metaSlot e) (metaSlot_injective e)
    (fun j => if j.val ≤ 8 then 0 else Rb) (fun _ => 0) (lentry e Rb input keys coords) (by
      intro j
      refine ⟨rfl, ?_⟩
      by_cases hj : j.val ≤ 8
      · rw [if_pos hj, ZeroPadding.pad_zero, lentry_meta e Rb input keys coords j hj]
      · rw [if_neg hj, lentry_high e Rb input keys coords _ (by simp [metaSlot, metaSlotVal, hj]; split_ifs <;> omega)]
        unfold metaIn
        rw [if_neg (by omega), dif_neg (by omega)])
  have out : ∀ (k : ℕ) (hk9 : 9 ≤ k) (hk : k ≤ 15),
      A ⟨k + 2, by omega⟩ = ZeroPadding.pad Rb (mA ⟨k, by omega⟩) ∧ H ⟨k + 2, by omega⟩ = mH ⟨k, by omega⟩ := by
    intro k hk9 hk
    have e1 : metaSlot e ⟨k, by omega⟩ = ⟨k + 2, by omega⟩ := by
      apply Fin.ext; simp [metaSlot, metaSlotVal]; split_ifs <;> omega
    have := o ⟨k, by omega⟩
    rw [e1] at this
    simp only [show ¬ (k ≤ 8) by omega, if_false] at this
    exact ⟨this.2, this.1⟩
  have free : ∀ i : Fin (117 + e), (i.val = 9 ∨ i.val = 10 ∨ (18 ≤ i.val ∧ i.val < 117)) →
      A i = lentry e Rb input keys coords i ∧ H i = 0 := by
    intro i hi
    have := kp i (by
      intro j hj
      have hv := congrArg Fin.val hj
      simp only [metaSlot, metaSlotVal] at hv
      split_ifs at hv <;> omega)
    exact ⟨this.2, this.1⟩
  refine ⟨H, A, st, ?_, ?_, ?_⟩
  · intro i hi
    by_cases h9 : i.val = 9
    · exact free i (Or.inl h9)
    · have e1 : metaSlot e ⟨i.val, by omega⟩ = i := by
        apply Fin.ext; simp [metaSlot, metaSlotVal]; omega
      have := o ⟨i.val, by omega⟩
      rw [e1] at this
      simp only [show i.val ≤ 8 by omega, if_true, ZeroPadding.pad_zero] at this
      rw [this.2, this.1]
      have hk' := hk ⟨i.val, by omega⟩ (by simp; omega)
      rw [hk'.1, hk'.2]
      refine ⟨?_, rfl⟩
      have hl := lentry_meta e Rb input keys coords ⟨i.val, by omega⟩ (by simp; omega)
      rw [e1] at hl
      exact hl.symm
  · intro i hi hi'
    rw [(free i (Or.inr (Or.inr ⟨hi, hi'⟩))).1, (free i (Or.inr (Or.inr ⟨hi, hi'⟩))).2,
      lentry_high e Rb input keys coords i (by omega)]
    exact ⟨rfl, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [(free ⟨10, by omega⟩ (by simp)).1, lentry_high e Rb input keys coords _ (by simp)]
  · exact (free ⟨10, by omega⟩ (by simp)).2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(out 9 (by omega) (by omega)).1, h9.1]
  · rw [(out 9 (by omega) (by omega)).2, h9.2]
  · rw [(out 10 (by omega) (by omega)).1, h10.1]
  · rw [(out 10 (by omega) (by omega)).2, h10.2]
  · rw [(out 11 (by omega) (by omega)).1, h11.1]
  · rw [(out 11 (by omega) (by omega)).2, h11.2]
  · rw [(out 12 (by omega) (by omega)).1, h12.1]
  · rw [(out 12 (by omega) (by omega)).2, h12.2]
  · rw [(out 13 (by omega) (by omega)).1, h13.1]
  · rw [(out 13 (by omega) (by omega)).2, h13.2]
  · rw [(out 14 (by omega) (by omega)).1, h14.1]
  · rw [(out 14 (by omega) (by omega)).2, h14.2]
  · rw [(out 15 (by omega) (by omega)).1, h15.1]
  · rw [(out 15 (by omega) (by omega)).2, h15.2]

end Stage1

/-! ## Addressing helpers -/

theorem addCases_lt {m n : ℕ} {α : Sort _} (f : Fin m → α) (g : Fin n → α) (i : Fin (m + n)) (h : i.val < m) :
    Fin.addCases (motive := fun _ => α) f g i = f ⟨i.val, h⟩ := by
  cases i with
  | mk iv hiv => exact Fin.addCases_left (m := m) (n := n) (motive := fun _ => α) ⟨iv, h⟩

/-- The engine slot of arena tape `j` is KitBoot's arena tape `j`. -/
theorem engSlot_arena (e : ℕ) (j : Fin 34) :
    engSlot e ⟨j.val, by omega⟩ = kbSlot e (KitBoot.outSlot j) := by
  rw [arena_local]
  apply Fin.ext
  simp only [engSlot, engSlotVal, show j.val < 34 from j.isLt, if_true]

/-! ## Stage 2: the arena -/

section Stage2
variable (e Rb C w m n : ℕ) (input : List Bool) (keys : Fin 8 → List Bool) (coords bits : List Bool)

def Facts2 (H : Fin (117 + e) → ℕ) (A : Fin (117 + e) → List Bool) : Prop :=
  (∀ i : Fin (117 + e), i.val ≤ 9 → A i = lentry e Rb input keys coords i ∧ H i = 0) ∧
  (∀ i : Fin (117 + e), 112 ≤ i.val → i.val < 117 → A i = ZeroPadding.pad Rb [] ∧ H i = 0) ∧
  A ⟨10, by omega⟩ = ZeroPadding.pad Rb [] ∧ H ⟨10, by omega⟩ = 0 ∧
  A ⟨14, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape m) ∧ H ⟨14, by omega⟩ = 0 ∧
  A ⟨15, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape n) ∧ H ⟨15, by omega⟩ = 0 ∧
  A ⟨16, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape (n * m)) ∧ H ⟨16, by omega⟩ = 0 ∧
  A ⟨17, by omega⟩ = ZeroPadding.pad Rb bits ∧ H ⟨17, by omega⟩ = n * m ∧
  ∀ j : Fin 34, A (engSlot e ⟨j.val, by omega⟩) =
      ZeroPadding.pad Rb (ReusableArithmetic.state C (commonReserve C w) [] [] j) ∧
    H (engSlot e ⟨j.val, by omega⟩) = ReusableArithmetic.heads j

theorem stage2 (H : Fin (117 + e) → ℕ) (A : Fin (117 + e) → List Bool)
    (f : Facts1 e Rb C w m n input keys coords bits H A) :
    ∃ (H' : Fin (117 + e) → ℕ) (A' : Fin (117 + e) → List Bool),
      Step (RecoveryFocus.machine (kbSlot e) KitBoot.machine) (KitBoot.cost C w) H A H' A' ∧
      Facts2 e Rb C w m n input keys coords bits H' A' := by
  obtain ⟨fb, ffree, fa10, fh10, fa11, fh11, fa12, fh12, fa13, fh13, fa14, fh14, fa15, fh15, fa16, fh16,
    fa17, fh17⟩ := f
  obtain ⟨kH, kA, ks, kout⟩ := KitBoot.run C w
  obtain ⟨H', A', st, o, kp⟩ := Dock.lift ks (kbSlot e) (kbSlot_injective e) (fun _ => Rb) H A (by
    intro k
    by_cases hk : k.val < 3
    · have hk3 : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by omega
      rcases hk3 with h | h | h
      · have e1 : kbSlot e k = ⟨11, by omega⟩ := Fin.ext (by simp [kbSlot, kbSlotVal, h])
        rw [e1, fa11, fh11]; refine ⟨rfl, ?_⟩; unfold KitBoot.entry; simp [h]
      · have e1 : kbSlot e k = ⟨12, by omega⟩ := Fin.ext (by simp [kbSlot, kbSlotVal, h])
        rw [e1, fa12, fh12]; refine ⟨rfl, ?_⟩; unfold KitBoot.entry; simp [h]
      · have e1 : kbSlot e k = ⟨13, by omega⟩ := Fin.ext (by simp [kbSlot, kbSlotVal, h])
        rw [e1, fa13, fh13]; refine ⟨rfl, ?_⟩; unfold KitBoot.entry; simp [h]
    · have hv : (kbSlot e k).val = 15 + k.val := by simp [kbSlot, kbSlotVal, hk]
      rw [(ffree _ (by omega) (by omega)).1, (ffree _ (by omega) (by omega)).2,
        KitBoot.entry_high C w k (by omega)]
      exact ⟨rfl, rfl⟩)
  have keep : ∀ i : Fin (117 + e), (i.val ≤ 10 ∨ (14 ≤ i.val ∧ i.val ≤ 17) ∨ 112 ≤ i.val) →
      A' i = A i ∧ H' i = H i := by
    intro i hi
    have := kp i (by
      intro k hk
      have hv := congrArg Fin.val hk
      simp only [kbSlot, kbSlotVal] at hv
      split_ifs at hv <;> omega)
    exact ⟨this.2, this.1⟩
  refine ⟨H', A', st, ?_, ?_, ?_⟩
  · intro i hi
    rw [(keep i (by omega)).1, (keep i (by omega)).2]
    exact fb i hi
  · intro i hi hi'
    rw [(keep i (by omega)).1, (keep i (by omega)).2]
    have := ffree i (by omega) hi'
    exact this
  refine ⟨(keep _ (by simp)).1.trans fa10, (keep _ (by simp)).2.trans fh10,
    (keep _ (by simp)).1.trans fa14, (keep _ (by simp)).2.trans fh14,
    (keep _ (by simp)).1.trans fa15, (keep _ (by simp)).2.trans fh15,
    (keep _ (by simp)).1.trans fa16, (keep _ (by simp)).2.trans fh16,
    (keep _ (by simp)).1.trans fa17, (keep _ (by simp)).2.trans fh17, ?_⟩
  intro j
  rw [engSlot_arena]
  have hi := o (KitBoot.outSlot j)
  have hk := kout j
  rw [hi.1, hi.2, hk.1, hk.2]
  exact ⟨rfl, rfl⟩

end Stage2

/-! ## Engine bank read-offs -/

theorem engA_arena (C R idx m : ℕ) (left acc : Poly) (ps : List Poly) (bits : List Bool) (P : Poly) (n : ℕ)
    (j : Fin 42) (hj : j.val < 34) :
    engA C R idx m left acc ps bits P n j =
      ReusableArithmetic.state C R (left.map (maskNat C)) (acc.map (maskNat C)) ⟨j.val, hj⟩ := by
  unfold engA bodyA TranscriptColumnLookupFold.A SelectedPairFetch.A OrderedPacketStep.A ArithmeticLookup.A
  rw [addCases_lt (m := 41) (n := 1) _ _ j (by omega)]
  rw [addCases_lt (m := 39) (n := 2) _ _ _ (by show j.val < 39; omega)]
  rw [addCases_lt (m := 38) (n := 1) _ _ _ (by show j.val < 38; omega)]
  rw [addCases_lt (m := 37) (n := 1) _ _ _ (by show j.val < 37; omega)]
  rw [addCases_lt (m := 34) (n := 3) _ _ _ (by show j.val < 34; omega)]

theorem engH_arena (pos : ℕ) (j : Fin 42) (hj : j.val < 34) :
    engH pos j = ReusableArithmetic.heads ⟨j.val, hj⟩ := by
  unfold engH bodyH TranscriptColumnLookupFold.H SelectedPairFetch.H
  rw [addCases_lt (m := 41) (n := 1) _ _ j (by omega)]
  rw [addCases_lt (m := 39) (n := 2) _ _ _ (by show j.val < 39; omega)]
  rw [addCases_lt (m := 38) (n := 1) _ _ _ (by show j.val < 38; omega)]
  rw [addCases_lt (m := 37) (n := 1) _ _ _ (by show j.val < 37; omega)]
  simp only [ArithmeticLookup.H, ReusableArithmetic.heads, Fin.ext_iff]
  split_ifs <;> simp_all

theorem tmpl_pad (Rb k : ℕ) (hk : k + 2 ≤ Rb) :
    ZeroPadding.pad Rb (UnaryTemplate.tape k) = ZeroPadding.pad Rb (CompareMachine.word k) := by
  have ht : UnaryTemplate.tape k = CompareMachine.word k ++ List.replicate 1 false := by
    simp [UnaryTemplate.tape, CompareMachine.word]
  rw [ht, Dock.pad_append_zeros Rb 1 _ (by simp [CompareMachine.word]; omega)]

theorem word_zero_pad (Rb R : ℕ) (hR : 1 ≤ R) (hRb : R ≤ Rb) :
    ZeroPadding.pad Rb (ZeroPadding.pad R (CompareMachine.word 0)) = ZeroPadding.pad Rb [] := by
  rw [Dock.pad_monotone R Rb _ hRb]
  exact Dock.pad_zeros Rb 1 (by omega)

/-! ## Stage 3: three head moves (index word, inner driver, outer driver) -/

section Stage3
variable (e Rb C w m n : ℕ) (input : List Bool) (keys : Fin 8 → List Bool) (coords bits : List Bool)

def Facts3 (H : Fin (117 + e) → ℕ) (A : Fin (117 + e) → List Bool) : Prop :=
  (∀ i : Fin (117 + e), i.val ≤ 9 → A i = lentry e Rb input keys coords i ∧ H i = 0) ∧
  (∀ i : Fin (117 + e), 112 ≤ i.val → i.val < 117 → A i = ZeroPadding.pad Rb [] ∧ H i = 0) ∧
  A ⟨10, by omega⟩ = ZeroPadding.pad Rb [] ∧ H ⟨10, by omega⟩ = 0 ∧
  A ⟨14, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape m) ∧ H ⟨14, by omega⟩ = 1 ∧
  A ⟨15, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape n) ∧ H ⟨15, by omega⟩ = 1 ∧
  A ⟨16, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape (n * m)) ∧ H ⟨16, by omega⟩ = 1 ∧
  A ⟨17, by omega⟩ = ZeroPadding.pad Rb bits ∧ H ⟨17, by omega⟩ = n * m ∧
  ∀ j : Fin 34, A (engSlot e ⟨j.val, by omega⟩) =
      ZeroPadding.pad Rb (ReusableArithmetic.state C (commonReserve C w) [] [] j) ∧
    H (engSlot e ⟨j.val, by omega⟩) = ReusableArithmetic.heads j

noncomputable def moves3 := Composition.machine (PhysicalIndexReload.move (t := 117 + e) ⟨14, by omega⟩ .right)
  (Composition.machine (PhysicalIndexReload.move (t := 117 + e) ⟨15, by omega⟩ .right)
    (PhysicalIndexReload.move (t := 117 + e) ⟨16, by omega⟩ .right))

theorem stage3 (H : Fin (117 + e) → ℕ) (A : Fin (117 + e) → List Bool)
    (f : Facts2 e Rb C w m n input keys coords bits H A) :
    ∃ (H' : Fin (117 + e) → ℕ), Step (moves3 e) (1 + 1 + (1 + 1 + 1)) H A H' A ∧
      Facts3 e Rb C w m n input keys coords bits H' A := by
  obtain ⟨fb, ffree, fa10, fh10, fa14, fh14, fa15, fh15, fa16, fh16, fa17, fh17, far⟩ := f
  have s1 := PhysicalIndexReload.move_run (⟨14, by omega⟩ : Fin (117 + e)) .right H A
  have s2 := PhysicalIndexReload.move_run (⟨15, by omega⟩ : Fin (117 + e)) .right
    (Function.update H ⟨14, by omega⟩ (HeadMove.right.apply (H ⟨14, by omega⟩))) A
  have s3 := PhysicalIndexReload.move_run (⟨16, by omega⟩ : Fin (117 + e)) .right
    (Function.update (Function.update H ⟨14, by omega⟩ (HeadMove.right.apply (H ⟨14, by omega⟩))) ⟨15, by omega⟩
      (HeadMove.right.apply ((Function.update H ⟨14, by omega⟩ (HeadMove.right.apply (H ⟨14, by omega⟩)))
        ⟨15, by omega⟩))) A
  refine ⟨_, s1.seq (s2.seq s3), ?_⟩
  have hH : ∀ i : Fin (117 + e), i.val ≠ 14 → i.val ≠ 15 → i.val ≠ 16 →
      (Function.update (Function.update (Function.update H ⟨14, by omega⟩ (HeadMove.right.apply (H ⟨14, by omega⟩)))
        ⟨15, by omega⟩ (HeadMove.right.apply ((Function.update H ⟨14, by omega⟩
          (HeadMove.right.apply (H ⟨14, by omega⟩))) ⟨15, by omega⟩))) ⟨16, by omega⟩
        (HeadMove.right.apply ((Function.update (Function.update H ⟨14, by omega⟩
          (HeadMove.right.apply (H ⟨14, by omega⟩))) ⟨15, by omega⟩ (HeadMove.right.apply
            ((Function.update H ⟨14, by omega⟩ (HeadMove.right.apply (H ⟨14, by omega⟩))) ⟨15, by omega⟩)))
          ⟨16, by omega⟩))) i = H i := by
    intro i h14 h15 h16
    rw [Function.update_of_ne (fun h => h16 (by rw [h])), Function.update_of_ne (fun h => h15 (by rw [h])),
      Function.update_of_ne (fun h => h14 (by rw [h]))]
  refine ⟨fun i hi => ⟨(fb i hi).1, (hH i (by omega) (by omega) (by omega)).trans (fb i hi).2⟩,
    fun i hi hi' => ⟨(ffree i hi hi').1, (hH i (by omega) (by omega) (by omega)).trans (ffree i hi hi').2⟩,
    fa10, (hH _ (by simp) (by simp) (by simp)).trans fh10, fa14, ?_, fa15, ?_, fa16, ?_, fa17,
    (hH _ (by simp) (by simp) (by simp)).trans fh17, ?_⟩
  · simp [fh14, HeadMove.apply]
  · simp [fh15, HeadMove.apply]
  · simp [fh16, HeadMove.apply]
  · intro j
    have hv : (engSlot e ⟨j.val, by omega⟩).val = if j.val = 32 then 62 else 66 + j.val := by
      simp [engSlot, engSlotVal, show j.val < 34 from j.isLt]
    refine ⟨(far j).1, (hH _ (by rw [hv]; split_ifs <;> omega) (by rw [hv]; split_ifs <;> omega)
      (by rw [hv]; split_ifs <;> omega)).trans (far j).2⟩

end Stage3

/-! ## Stage 4: the SYM engine (docked) -/

section Stage4
variable (e Rb C w m n : ℕ) (input : List Bool) (keys : Fin 8 → List Bool) (coords bits : List Bool)

def Facts4 (Pf : Poly) (H : Fin (117 + e) → ℕ) (A : Fin (117 + e) → List Bool) : Prop :=
  (∀ i : Fin (117 + e), i.val ≤ 9 → A i = lentry e Rb input keys coords i ∧ H i = 0) ∧
  (∀ i : Fin (117 + e), 115 ≤ i.val → i.val < 117 → A i = ZeroPadding.pad Rb [] ∧ H i = 0) ∧
  A ⟨10, by omega⟩ = ZeroPadding.pad Rb [] ∧ H ⟨10, by omega⟩ = 0 ∧
  A ⟨14, by omega⟩ = ZeroPadding.pad Rb (CompareMachine.word m) ∧ H ⟨14, by omega⟩ = 1 ∧
  A ⟨97, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape (commonReserve C w)) ∧ H ⟨97, by omega⟩ = 1 ∧
  A ⟨113, by omega⟩ = ZeroPadding.pad Rb (ZeroPadding.pad (commonReserve C w) (Pf.map (maskNat C)).flatten) ∧
    H ⟨113, by omega⟩ = 0 ∧
  A ⟨114, by omega⟩ = ZeroPadding.pad Rb (ZeroPadding.pad (commonReserve C w) (CompareMachine.word Pf.length)) ∧
    H ⟨114, by omega⟩ = 0

theorem lentry_nine (e Rb : ℕ) (input : List Bool) (keys : Fin 8 → List Bool) (coords : List Bool) :
    lentry e Rb input keys coords ⟨9, by omega⟩ = ZeroPadding.pad Rb coords := by
  simp [lentry]

/-- The engine's entry, read off at every engine slot from `Facts3`. -/
theorem stage4_hin (ps : List Poly) (hcoords : coords = OrderedPacketStep.bank C (commonReserve C w) ps)
    (hR1 : 1 ≤ commonReserve C w) (hRb : commonReserve C w ≤ Rb) (hnm : n * m + 2 ≤ commonReserve C w)
    (hm2 : m + 2 ≤ Rb) (hn2 : n + 2 ≤ Rb)
    (H : Fin (117 + e) → ℕ) (A : Fin (117 + e) → List Bool)
    (f : Facts3 e Rb C w m n input keys coords bits H A) (j : Fin 42) :
    H (engSlot e j) = engH (n * m) j ∧
      A (engSlot e j) = ZeroPadding.pad Rb (engA C (commonReserve C w) (n * m) m [] [] ps bits [] n j) := by
  obtain ⟨fb, ffree, _, _, fa14, fh14, fa15, fh15, fa16, fh16, fa17, fh17, far⟩ := f
  by_cases hj : j.val < 34
  · have fj := far ⟨j.val, hj⟩
    have ej : (⟨(⟨j.val, hj⟩ : Fin 34).val, by omega⟩ : Fin 42) = j := Fin.ext rfl
    rw [ej] at fj
    rw [engA_arena _ _ _ _ _ _ _ _ _ _ j hj, engH_arena _ j hj]
    exact ⟨fj.2, fj.1⟩
  · obtain ⟨k, hk⟩ := j
    simp only at hj
    interval_cases k
    · refine ⟨(fb ⟨9, by omega⟩ (by simp)).2, ?_⟩
      show A ⟨9, by omega⟩ = _
      rw [(fb ⟨9, by omega⟩ (by simp)).1, lentry_nine, hcoords]
      rfl
    · refine ⟨fh16, ?_⟩
      show A ⟨16, by omega⟩ = ZeroPadding.pad Rb (ZeroPadding.pad (commonReserve C w) (CompareMachine.word (n * m)))
      rw [fa16, Dock.pad_monotone _ Rb _ hRb, tmpl_pad Rb (n * m) (by omega)]
    · refine ⟨(ffree ⟨112, by omega⟩ (by simp) (by simp)).2, ?_⟩
      show A ⟨112, by omega⟩ = ZeroPadding.pad Rb (List.replicate (commonReserve C w) false)
      rw [(ffree ⟨112, by omega⟩ (by simp) (by simp)).1, Dock.pad_zeros Rb _ hRb]
    · exact ⟨fh17, fa17⟩
    · refine ⟨fh14, ?_⟩
      show A ⟨14, by omega⟩ = ZeroPadding.pad Rb (CompareMachine.word m)
      rw [fa14, tmpl_pad Rb m hm2]
    · refine ⟨(ffree ⟨113, by omega⟩ (by simp) (by simp)).2, ?_⟩
      show A ⟨113, by omega⟩ = ZeroPadding.pad Rb (ZeroPadding.pad (commonReserve C w)
        (([] : Poly).map (maskNat C)).flatten)
      rw [(ffree ⟨113, by omega⟩ (by simp) (by simp)).1, List.map_nil, List.flatten_nil,
        Dock.pad_monotone _ Rb _ hRb]
    · refine ⟨(ffree ⟨114, by omega⟩ (by simp) (by simp)).2, ?_⟩
      show A ⟨114, by omega⟩ = ZeroPadding.pad Rb (ZeroPadding.pad (commonReserve C w)
        (CompareMachine.word ([] : Poly).length))
      rw [(ffree ⟨114, by omega⟩ (by simp) (by simp)).1, List.length_nil, word_zero_pad Rb _ hR1 hRb]
    · refine ⟨fh15, ?_⟩
      show A ⟨15, by omega⟩ = ZeroPadding.pad Rb (CompareMachine.word n)
      rw [fa15, tmpl_pad Rb n hn2]

theorem stage4 (S : Finset ℕ) (d : ℕ) (ps : List Poly)
    (hcoords : coords = OrderedPacketStep.bank C (commonReserve C w) ps)
    (hS : ∀ j ∈ S, j < C) (hps : ∀ P ∈ ps, NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card + 1) ^ d ≤ 2 ^ w) (hfitn : (S.card + 1) ^ (d * n) ≤ 2 ^ w)
    (hlen : n * m ≤ ps.length) (hN : ps.length ≤ 2 ^ w) (hw : 1 ≤ w)
    (hR1 : 1 ≤ commonReserve C w) (hRb : commonReserve C w ≤ Rb) (hnm : n * m + 2 ≤ commonReserve C w)
    (hm2 : m + 2 ≤ Rb) (hn2 : n + 2 ≤ Rb)
    (H : Fin (117 + e) → ℕ) (A : Fin (117 + e) → List Bool)
    (f : Facts3 e Rb C w m n input keys coords bits H A) :
    ∃ (H' : Fin (117 + e) → ℕ) (A' : Fin (117 + e) → List Bool),
      Step (RecoveryFocus.machine (engSlot e) symEngine) (symEngineCost C w n m) H A H' A' ∧
      (∀ j, H' (engSlot e j) = engH 0 j ∧ A' (engSlot e j) = ZeroPadding.pad Rb
        (engA C (commonReserve C w) 0 m (leftAt ps bits n m [] n) [] ps bits
          (Normalized.structuralGF2Product (blockPolys ps bits n m)) n j)) ∧
      (∀ i, (∀ j, engSlot e j ≠ i) → H' i = H i ∧ A' i = A i) :=
  Dock.lift (symEngine_run C w S d ps bits n m hS hps hfit hfitn hlen hN hw)
    (engSlot e) (engSlot_injective e) (fun _ => Rb) H A
    (stage4_hin e Rb C w m n input keys coords bits ps hcoords hR1 hRb hnm hm2 hn2 H A f)

theorem engSlot_avoid (e : ℕ) (i : Fin (117 + e)) (hi : i.val ≤ 8 ∨ i.val = 10 ∨ 115 ≤ i.val) :
    ∀ j, engSlot e j ≠ i := by
  intro j hj
  have hv := congrArg Fin.val hj
  simp only [engSlot, engSlotVal] at hv
  split_ifs at hv <;> omega

/-- The facts the store needs, from the engine's output. -/
theorem stage4_facts (ps : List Poly) (hcoords : coords = OrderedPacketStep.bank C (commonReserve C w) ps)
    (H A : _) (f : Facts3 e Rb C w m n input keys coords bits H A)
    (H' : Fin (117 + e) → ℕ) (A' : Fin (117 + e) → List Bool)
    (o : ∀ j, H' (engSlot e j) = engH 0 j ∧ A' (engSlot e j) = ZeroPadding.pad Rb
        (engA C (commonReserve C w) 0 m (leftAt ps bits n m [] n) [] ps bits
          (Normalized.structuralGF2Product (blockPolys ps bits n m)) n j))
    (kp : ∀ i, (∀ j, engSlot e j ≠ i) → H' i = H i ∧ A' i = A i) :
    Facts4 e Rb C w m input keys coords (Normalized.structuralGF2Product (blockPolys ps bits n m)) H' A' := by
  obtain ⟨fb, ffree, fa10, fh10, _⟩ := f
  have keep : ∀ i : Fin (117 + e), (i.val ≤ 8 ∨ i.val = 10 ∨ 115 ≤ i.val) → A' i = A i ∧ H' i = H i := by
    intro i hi
    have := kp i (engSlot_avoid e i hi)
    exact ⟨this.2, this.1⟩
  refine ⟨?_, ?_, (keep _ (by simp)).1.trans fa10, (keep _ (by simp)).2.trans fh10, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    by_cases h9 : i.val = 9
    · have ei : i = engSlot e ⟨34, by omega⟩ := Fin.ext h9
      rw [ei, (o _).1, (o _).2]
      refine ⟨?_, rfl⟩
      have e9 : engSlot e ⟨34, by omega⟩ = ⟨9, by omega⟩ := Fin.ext rfl
      rw [e9, lentry_nine, hcoords]
      rfl
    · rw [(keep i (by omega)).1, (keep i (by omega)).2]
      exact fb i hi
  · intro i hi hi'
    rw [(keep i (by omega)).1, (keep i (by omega)).2]
    exact ffree i (by omega) hi'
  · exact (o ⟨38, by omega⟩).2
  · exact (o ⟨38, by omega⟩).1
  · have h := (o ⟨31, by omega⟩).2
    have e31 : engSlot e ⟨31, by omega⟩ = ⟨97, by omega⟩ := Fin.ext rfl
    rw [e31, engA_arena _ _ _ _ _ _ _ _ _ _ _ (by simp)] at h
    exact h
  · have h := (o ⟨31, by omega⟩).1
    have e31 : engSlot e ⟨31, by omega⟩ = ⟨97, by omega⟩ := Fin.ext rfl
    rw [e31, engH_arena _ _ (by simp)] at h
    exact h
  · exact (o ⟨39, by omega⟩).2
  · exact (o ⟨39, by omega⟩).1
  · exact (o ⟨40, by omega⟩).2
  · exact (o ⟨40, by omega⟩).1

end Stage4

/-! ## Stages 5–6: the parked register into the output tape -/

section Stage6
variable (e Rb C w m : ℕ) (input : List Bool) (keys : Fin 8 → List Bool) (coords : List Bool)

theorem stoSlot_avoid (e : ℕ) (i : Fin (117 + e)) (hi : i.val ≤ 9) : ∀ j, stoSlot e j ≠ i := by
  intro j hj
  have hv := congrArg Fin.val hj
  simp only [stoSlot, stoSlotVal] at hv
  split_ifs at hv <;> omega

theorem stage56 (Pf : Poly) (hPf : Pf.length ≤ 2 ^ w) (hRb : PacketBank.storeBudget (commonReserve C w) ≤ Rb)
    (H : Fin (117 + e) → ℕ) (A : Fin (117 + e) → List Bool)
    (f : Facts4 e Rb C w m input keys coords Pf H A) :
    ∃ (H' : Fin (117 + e) → ℕ) (A' : Fin (117 + e) → List Bool),
      Step (Composition.machine (PhysicalIndexReload.move (t := 117 + e) ⟨114, by omega⟩ .right)
        (RecoveryFocus.machine (stoSlot e) symStore)) (1 + 1 + (2 * PacketBank.storeBudget (commonReserve C w) + 2))
        H A H' A' ∧
      (∀ i : Fin (117 + e), i.val ≤ 9 → A' i = lentry e Rb input keys coords i ∧ H' i = 0) ∧
      A' ⟨10, by omega⟩ = ZeroPadding.pad Rb (ZeroPadding.pad (commonReserve C w) (Pf.map (maskNat C)).flatten ++
        ZeroPadding.pad (commonReserve C w) (CompareMachine.word Pf.length)) ∧
      H' ⟨10, by omega⟩ = 0 := by
  obtain ⟨fb, ffree, fa10, fh10, fa14, fh14, fa97, fh97, fa113, fh113, fa114, fh114⟩ := f
  set R := commonReserve C w with hRdef
  have s5 := PhysicalIndexReload.move_run (⟨114, by omega⟩ : Fin (117 + e)) .right H A
  set H5 := Function.update H ⟨114, by omega⟩ (HeadMove.right.apply (H ⟨114, by omega⟩)) with hH5
  have h5 : ∀ i : Fin (117 + e), i.val ≠ 114 → H5 i = H i := by
    intro i hi
    rw [hH5, Function.update_of_ne (fun h => hi (by rw [h]))]
  have h5' : H5 ⟨114, by omega⟩ = 1 := by
    rw [hH5, Function.update_self, fh114]; rfl
  have lens := reg_lengths C w Pf hPf
  obtain ⟨H', A', st, o, kp⟩ := Dock.lift (symStore_run R m _ _ lens.1 lens.2) (stoSlot e) (stoSlot_injective e)
    (fun _ => Rb) H5 A (by
      intro j
      obtain ⟨k, hk⟩ := j
      interval_cases k
      · show H5 ⟨97, by omega⟩ = _ ∧ A ⟨97, by omega⟩ = _
        refine ⟨(h5 _ (by simp)).trans fh97, ?_⟩
        rw [fa97]; rfl
      · show H5 ⟨10, by omega⟩ = _ ∧ A ⟨10, by omega⟩ = _
        refine ⟨(h5 _ (by simp)).trans fh10, ?_⟩
        rw [fa10]; rfl
      · show H5 ⟨113, by omega⟩ = _ ∧ A ⟨113, by omega⟩ = _
        refine ⟨(h5 _ (by simp)).trans fh113, ?_⟩
        rw [fa113]; rfl
      · show H5 ⟨114, by omega⟩ = _ ∧ A ⟨114, by omega⟩ = _
        refine ⟨h5', ?_⟩
        rw [fa114]; rfl
      · show H5 ⟨14, by omega⟩ = _ ∧ A ⟨14, by omega⟩ = _
        refine ⟨(h5 _ (by simp)).trans fh14, ?_⟩
        rw [fa14]; rfl
      · show H5 ⟨115, by omega⟩ = _ ∧ A ⟨115, by omega⟩ = _
        refine ⟨(h5 _ (by simp)).trans (ffree ⟨115, by omega⟩ (by simp) (by simp)).2, ?_⟩
        rw [(ffree ⟨115, by omega⟩ (by simp) (by simp)).1]; rfl
      · show H5 ⟨116, by omega⟩ = _ ∧ A ⟨116, by omega⟩ = ZeroPadding.pad Rb (List.replicate (PacketBank.storeBudget R) false)
        refine ⟨(h5 _ (by simp)).trans (ffree ⟨116, by omega⟩ (by simp) (by simp)).2, ?_⟩
        rw [(ffree ⟨116, by omega⟩ (by simp) (by simp)).1, Dock.pad_zeros Rb _ hRb])
  refine ⟨H', A', s5.seq st, ?_, ?_, ?_⟩
  · intro i hi
    have := kp i (stoSlot_avoid e i hi)
    rw [this.1, this.2, h5 i (by omega)]
    exact fb i hi
  · have h := (o ⟨1, by omega⟩).2
    have e1 : stoSlot e ⟨1, by omega⟩ = ⟨10, by omega⟩ := Fin.ext rfl
    rw [e1] at h
    rw [h]
    rfl
  · have h := (o ⟨1, by omega⟩).1
    have e1 : stoSlot e ⟨1, by omega⟩ = ⟨10, by omega⟩ := Fin.ext rfl
    rw [e1] at h
    rw [h]
    rfl

end Stage6

end
end NearCubicWires.PacketsCombine

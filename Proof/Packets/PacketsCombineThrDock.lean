import Proof.Packets.PacketsCombineThrLocal

/-! # P2 (iii) assembly, part 2: the THR stage's local run, docked stage by stage (padded world)

Consumer: `ThrCombineStageK` (`PacketsCombineThrStage`). Same six stages as the SYM stage
(`PacketsCombineSymDock`) on the THR local layout (`PacketsCombineThrLocal`): metadata → `KitBoot` →
three head moves (index tape, inner and outer drivers) → the exact THR engine `thrLoop` → one head move →
the masked store (`symStore`, the same generic machine). Generic in the row's data (input, key words,
coordinate bank, table, `C`, `w`, `K`, `N`). Bookkeeping over donors; budget class: source-polynomial.
-/
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

/-- The THR local entry. -/
def tlentry (i : Fin (118 + e)) : List Bool :=
  if i.val = 0 then input
  else if h : 1 ≤ i.val ∧ i.val ≤ 8 then keys ⟨i.val - 1, by omega⟩
  else if i.val = 9 then ZeroPadding.pad Rb coords else ZeroPadding.pad Rb []

theorem tlentry_high (i : Fin (118 + e)) (h : 10 ≤ i.val) :
    tlentry e Rb input keys coords i = ZeroPadding.pad Rb [] := by
  unfold tlentry
  rw [if_neg (by omega), dif_neg (by omega), if_neg (by omega)]

theorem tlentry_nine : tlentry e Rb input keys coords ⟨9, by omega⟩ = ZeroPadding.pad Rb coords := by
  simp [tlentry]

theorem tlentry_meta (j : Fin (16 + e)) (hj : j.val ≤ 8) :
    tlentry e Rb input keys coords (tmetaSlot e j) = metaIn e input keys j := by
  have hv : (tmetaSlot e j).val = j.val := by simp [tmetaSlot, tmetaSlotVal, hj]
  unfold tlentry metaIn
  simp only [hv]
  split_ifs <;> first | rfl | omega

end Local

/-! ## Stage 1: the metadata -/

section Stage1
variable (e Rb C w K N : ℕ) (input : List Bool) (keys : Fin 8 → List Bool) (coords table : List Bool)

def TFacts1 (H : Fin (118 + e) → ℕ) (A : Fin (118 + e) → List Bool) : Prop :=
  (∀ i : Fin (118 + e), i.val ≤ 9 → A i = tlentry e Rb input keys coords i ∧ H i = 0) ∧
  (∀ i : Fin (118 + e), 18 ≤ i.val → i.val < 118 → A i = ZeroPadding.pad Rb [] ∧ H i = 0) ∧
  A ⟨10, by omega⟩ = ZeroPadding.pad Rb [] ∧ H ⟨10, by omega⟩ = 0 ∧
  A ⟨11, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape C) ∧ H ⟨11, by omega⟩ = 0 ∧
  A ⟨12, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape C) ∧ H ⟨12, by omega⟩ = 0 ∧
  A ⟨13, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape w) ∧ H ⟨13, by omega⟩ = 0 ∧
  A ⟨14, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape K) ∧ H ⟨14, by omega⟩ = 0 ∧
  A ⟨15, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape K) ∧ H ⟨15, by omega⟩ = 0 ∧
  A ⟨16, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape N) ∧ H ⟨16, by omega⟩ = 0 ∧
  A ⟨17, by omega⟩ = ZeroPadding.pad Rb table ∧ H ⟨17, by omega⟩ = N * (K + 1)

theorem tstage1 {s : ℕ} (M : Machine (16 + e) s) (mcost : ℕ) (mH : Fin (16 + e) → ℕ)
    (mA : Fin (16 + e) → List Bool)
    (hm : Step M mcost (fun _ => 0) (metaIn e input keys) mH mA)
    (hk : ∀ i : Fin (16 + e), i.val ≤ 8 → mA i = metaIn e input keys i ∧ mH i = 0)
    (h9 : mA ⟨9, by omega⟩ = UnaryTemplate.tape C ∧ mH ⟨9, by omega⟩ = 0)
    (h10 : mA ⟨10, by omega⟩ = UnaryTemplate.tape C ∧ mH ⟨10, by omega⟩ = 0)
    (h11 : mA ⟨11, by omega⟩ = UnaryTemplate.tape w ∧ mH ⟨11, by omega⟩ = 0)
    (h12 : mA ⟨12, by omega⟩ = UnaryTemplate.tape K ∧ mH ⟨12, by omega⟩ = 0)
    (h13 : mA ⟨13, by omega⟩ = UnaryTemplate.tape K ∧ mH ⟨13, by omega⟩ = 0)
    (h14 : mA ⟨14, by omega⟩ = UnaryTemplate.tape N ∧ mH ⟨14, by omega⟩ = 0)
    (h15 : mA ⟨15, by omega⟩ = table ∧ mH ⟨15, by omega⟩ = N * (K + 1)) :
    ∃ (H : Fin (118 + e) → ℕ) (A : Fin (118 + e) → List Bool),
      Step (RecoveryFocus.machine (tmetaSlot e) M) mcost (fun _ => 0) (tlentry e Rb input keys coords) H A ∧
      TFacts1 e Rb C w K N input keys coords table H A := by
  obtain ⟨H, A, st, o, kp⟩ := Dock.lift hm (tmetaSlot e) (tmetaSlot_injective e)
    (fun j => if j.val ≤ 8 then 0 else Rb) (fun _ => 0) (tlentry e Rb input keys coords) (by
      intro j
      refine ⟨rfl, ?_⟩
      by_cases hj : j.val ≤ 8
      · rw [if_pos hj, ZeroPadding.pad_zero, tlentry_meta e Rb input keys coords j hj]
      · rw [if_neg hj, tlentry_high e Rb input keys coords _ (by simp [tmetaSlot, tmetaSlotVal, hj]; split_ifs <;> omega)]
        unfold metaIn
        rw [if_neg (by omega), dif_neg (by omega)])
  have out : ∀ (k : ℕ) (hk9 : 9 ≤ k) (hk : k ≤ 15),
      A ⟨k + 2, by omega⟩ = ZeroPadding.pad Rb (mA ⟨k, by omega⟩) ∧ H ⟨k + 2, by omega⟩ = mH ⟨k, by omega⟩ := by
    intro k hk9 hk
    have e1 : tmetaSlot e ⟨k, by omega⟩ = ⟨k + 2, by omega⟩ := by
      apply Fin.ext; simp [tmetaSlot, tmetaSlotVal]; split_ifs <;> omega
    have := o ⟨k, by omega⟩
    rw [e1] at this
    simp only [show ¬ (k ≤ 8) by omega, if_false] at this
    exact ⟨this.2, this.1⟩
  have free : ∀ i : Fin (118 + e), (i.val = 9 ∨ i.val = 10 ∨ (18 ≤ i.val ∧ i.val < 118)) →
      A i = tlentry e Rb input keys coords i ∧ H i = 0 := by
    intro i hi
    have := kp i (by
      intro j hj
      have hv := congrArg Fin.val hj
      simp only [tmetaSlot, tmetaSlotVal] at hv
      split_ifs at hv <;> omega)
    exact ⟨this.2, this.1⟩
  refine ⟨H, A, st, ?_, ?_, ?_⟩
  · intro i hi
    by_cases h9 : i.val = 9
    · exact free i (Or.inl h9)
    · have e1 : tmetaSlot e ⟨i.val, by omega⟩ = i := by
        apply Fin.ext; simp [tmetaSlot, tmetaSlotVal]; omega
      have := o ⟨i.val, by omega⟩
      rw [e1] at this
      simp only [show i.val ≤ 8 by omega, if_true, ZeroPadding.pad_zero] at this
      rw [this.2, this.1]
      have hk' := hk ⟨i.val, by omega⟩ (by simp; omega)
      rw [hk'.1, hk'.2]
      refine ⟨?_, rfl⟩
      have hl := tlentry_meta e Rb input keys coords ⟨i.val, by omega⟩ (by simp; omega)
      rw [e1] at hl
      exact hl.symm
  · intro i hi hi'
    rw [(free i (Or.inr (Or.inr ⟨hi, hi'⟩))).1, (free i (Or.inr (Or.inr ⟨hi, hi'⟩))).2,
      tlentry_high e Rb input keys coords i (by omega)]
    exact ⟨rfl, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [(free ⟨10, by omega⟩ (by simp)).1, tlentry_high e Rb input keys coords _ (by simp)]
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

/-! ## Stage 2: the arena -/

section Stage2
variable (e Rb C w K N : ℕ) (input : List Bool) (keys : Fin 8 → List Bool) (coords table : List Bool)

def TFacts2 (H : Fin (118 + e) → ℕ) (A : Fin (118 + e) → List Bool) : Prop :=
  (∀ i : Fin (118 + e), i.val ≤ 9 → A i = tlentry e Rb input keys coords i ∧ H i = 0) ∧
  (∀ i : Fin (118 + e), 112 ≤ i.val → i.val < 118 → A i = ZeroPadding.pad Rb [] ∧ H i = 0) ∧
  A ⟨10, by omega⟩ = ZeroPadding.pad Rb [] ∧ H ⟨10, by omega⟩ = 0 ∧
  A ⟨14, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape K) ∧ H ⟨14, by omega⟩ = 0 ∧
  A ⟨15, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape K) ∧ H ⟨15, by omega⟩ = 0 ∧
  A ⟨16, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape N) ∧ H ⟨16, by omega⟩ = 0 ∧
  A ⟨17, by omega⟩ = ZeroPadding.pad Rb table ∧ H ⟨17, by omega⟩ = N * (K + 1) ∧
  ∀ j : Fin 34, A (tengSlot e ⟨j.val, by omega⟩) =
      ZeroPadding.pad Rb (ReusableArithmetic.state C (commonReserve C w) [] [] j) ∧
    H (tengSlot e ⟨j.val, by omega⟩) = ReusableArithmetic.heads j

theorem tstage2 (H : Fin (118 + e) → ℕ) (A : Fin (118 + e) → List Bool)
    (f : TFacts1 e Rb C w K N input keys coords table H A) :
    ∃ (H' : Fin (118 + e) → ℕ) (A' : Fin (118 + e) → List Bool),
      Step (RecoveryFocus.machine (tkbSlot e) KitBoot.machine) (KitBoot.cost C w) H A H' A' ∧
      TFacts2 e Rb C w K N input keys coords table H' A' := by
  obtain ⟨fb, ffree, fa10, fh10, fa11, fh11, fa12, fh12, fa13, fh13, fa14, fh14, fa15, fh15, fa16, fh16,
    fa17, fh17⟩ := f
  obtain ⟨kH, kA, ks, kout⟩ := KitBoot.run C w
  obtain ⟨H', A', st, o, kp⟩ := Dock.lift ks (tkbSlot e) (tkbSlot_injective e) (fun _ => Rb) H A (by
    intro k
    by_cases hk : k.val < 3
    · have hk3 : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by omega
      rcases hk3 with h | h | h
      · have e1 : tkbSlot e k = ⟨11, by omega⟩ := Fin.ext (by simp [tkbSlot, kbSlotVal, h])
        rw [e1, fa11, fh11]; refine ⟨rfl, ?_⟩; unfold KitBoot.entry; simp [h]
      · have e1 : tkbSlot e k = ⟨12, by omega⟩ := Fin.ext (by simp [tkbSlot, kbSlotVal, h])
        rw [e1, fa12, fh12]; refine ⟨rfl, ?_⟩; unfold KitBoot.entry; simp [h]
      · have e1 : tkbSlot e k = ⟨13, by omega⟩ := Fin.ext (by simp [tkbSlot, kbSlotVal, h])
        rw [e1, fa13, fh13]; refine ⟨rfl, ?_⟩; unfold KitBoot.entry; simp [h]
    · have hv : (tkbSlot e k).val = 15 + k.val := by simp [tkbSlot, kbSlotVal, hk]
      rw [(ffree _ (by omega) (by omega)).1, (ffree _ (by omega) (by omega)).2,
        KitBoot.entry_high C w k (by omega)]
      exact ⟨rfl, rfl⟩)
  have keep : ∀ i : Fin (118 + e), (i.val ≤ 10 ∨ (14 ≤ i.val ∧ i.val ≤ 17) ∨ 112 ≤ i.val) →
      A' i = A i ∧ H' i = H i := by
    intro i hi
    have := kp i (by
      intro k hk
      have hv := congrArg Fin.val hk
      simp only [tkbSlot, kbSlotVal] at hv
      split_ifs at hv <;> omega)
    exact ⟨this.2, this.1⟩
  refine ⟨H', A', st, ?_, ?_, ?_⟩
  · intro i hi
    rw [(keep i (by omega)).1, (keep i (by omega)).2]
    exact fb i hi
  · intro i hi hi'
    rw [(keep i (by omega)).1, (keep i (by omega)).2]
    exact ffree i (by omega) hi'
  refine ⟨(keep _ (by simp)).1.trans fa10, (keep _ (by simp)).2.trans fh10,
    (keep _ (by simp)).1.trans fa14, (keep _ (by simp)).2.trans fh14,
    (keep _ (by simp)).1.trans fa15, (keep _ (by simp)).2.trans fh15,
    (keep _ (by simp)).1.trans fa16, (keep _ (by simp)).2.trans fh16,
    (keep _ (by simp)).1.trans fa17, (keep _ (by simp)).2.trans fh17, ?_⟩
  intro j
  rw [tengSlot_arena]
  have hi := o (KitBoot.outSlot j)
  have hk := kout j
  rw [hi.1, hi.2, hk.1, hk.2]
  exact ⟨rfl, rfl⟩

end Stage2

/-! ## Stage 3: three head moves (index tape, inner driver, outer driver) -/

section Stage3
variable (e Rb C w K N : ℕ) (input : List Bool) (keys : Fin 8 → List Bool) (coords table : List Bool)

def TFacts3 (H : Fin (118 + e) → ℕ) (A : Fin (118 + e) → List Bool) : Prop :=
  (∀ i : Fin (118 + e), i.val ≤ 9 → A i = tlentry e Rb input keys coords i ∧ H i = 0) ∧
  (∀ i : Fin (118 + e), 112 ≤ i.val → i.val < 118 → i.val ≠ 113 → A i = ZeroPadding.pad Rb [] ∧ H i = 0) ∧
  A ⟨113, by omega⟩ = ZeroPadding.pad Rb [] ∧ H ⟨113, by omega⟩ = 1 ∧
  A ⟨10, by omega⟩ = ZeroPadding.pad Rb [] ∧ H ⟨10, by omega⟩ = 0 ∧
  A ⟨14, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape K) ∧ H ⟨14, by omega⟩ = 0 ∧
  A ⟨15, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape K) ∧ H ⟨15, by omega⟩ = 1 ∧
  A ⟨16, by omega⟩ = ZeroPadding.pad Rb (UnaryTemplate.tape N) ∧ H ⟨16, by omega⟩ = 1 ∧
  A ⟨17, by omega⟩ = ZeroPadding.pad Rb table ∧ H ⟨17, by omega⟩ = N * (K + 1) ∧
  ∀ j : Fin 34, A (tengSlot e ⟨j.val, by omega⟩) =
      ZeroPadding.pad Rb (ReusableArithmetic.state C (commonReserve C w) [] [] j) ∧
    H (tengSlot e ⟨j.val, by omega⟩) = ReusableArithmetic.heads j

noncomputable def tmoves3 := Composition.machine (PhysicalIndexReload.move (t := 118 + e) ⟨113, by omega⟩ .right)
  (Composition.machine (PhysicalIndexReload.move (t := 118 + e) ⟨15, by omega⟩ .right)
    (PhysicalIndexReload.move (t := 118 + e) ⟨16, by omega⟩ .right))

theorem tstage3 (H : Fin (118 + e) → ℕ) (A : Fin (118 + e) → List Bool)
    (f : TFacts2 e Rb C w K N input keys coords table H A) :
    ∃ (H' : Fin (118 + e) → ℕ), Step (tmoves3 e) (1 + 1 + (1 + 1 + 1)) H A H' A ∧
      TFacts3 e Rb C w K N input keys coords table H' A := by
  obtain ⟨fb, ffree, fa10, fh10, fa14, fh14, fa15, fh15, fa16, fh16, fa17, fh17, far⟩ := f
  have s1 := PhysicalIndexReload.move_run (⟨113, by omega⟩ : Fin (118 + e)) .right H A
  have s2 := PhysicalIndexReload.move_run (⟨15, by omega⟩ : Fin (118 + e)) .right
    (Function.update H ⟨113, by omega⟩ (HeadMove.right.apply (H ⟨113, by omega⟩))) A
  have s3 := PhysicalIndexReload.move_run (⟨16, by omega⟩ : Fin (118 + e)) .right
    (Function.update (Function.update H ⟨113, by omega⟩ (HeadMove.right.apply (H ⟨113, by omega⟩))) ⟨15, by omega⟩
      (HeadMove.right.apply ((Function.update H ⟨113, by omega⟩ (HeadMove.right.apply (H ⟨113, by omega⟩)))
        ⟨15, by omega⟩))) A
  refine ⟨_, s1.seq (s2.seq s3), ?_⟩
  have hH : ∀ i : Fin (118 + e), i.val ≠ 113 → i.val ≠ 15 → i.val ≠ 16 →
      (Function.update (Function.update (Function.update H ⟨113, by omega⟩ (HeadMove.right.apply (H ⟨113, by omega⟩)))
        ⟨15, by omega⟩ (HeadMove.right.apply ((Function.update H ⟨113, by omega⟩
          (HeadMove.right.apply (H ⟨113, by omega⟩))) ⟨15, by omega⟩))) ⟨16, by omega⟩
        (HeadMove.right.apply ((Function.update (Function.update H ⟨113, by omega⟩
          (HeadMove.right.apply (H ⟨113, by omega⟩))) ⟨15, by omega⟩ (HeadMove.right.apply
            ((Function.update H ⟨113, by omega⟩ (HeadMove.right.apply (H ⟨113, by omega⟩))) ⟨15, by omega⟩)))
          ⟨16, by omega⟩))) i = H i := by
    intro i h113 h15 h16
    rw [Function.update_of_ne (fun h => h16 (by rw [h])), Function.update_of_ne (fun h => h15 (by rw [h])),
      Function.update_of_ne (fun h => h113 (by rw [h]))]
  have f113 := ffree ⟨113, by omega⟩ (by simp) (by simp)
  refine ⟨fun i hi => ⟨(fb i hi).1, (hH i (by omega) (by omega) (by omega)).trans (fb i hi).2⟩,
    fun i hi hi' hn => ⟨(ffree i hi hi').1, (hH i hn (by omega) (by omega)).trans (ffree i hi hi').2⟩,
    f113.1, ?_, fa10, (hH _ (by simp) (by simp) (by simp)).trans fh10, fa14,
    (hH _ (by simp) (by simp) (by simp)).trans fh14, fa15, ?_, fa16, ?_, fa17,
    (hH _ (by simp) (by simp) (by simp)).trans fh17, ?_⟩
  · simp [f113.2, HeadMove.apply]
  · simp [fh15, HeadMove.apply]
  · simp [fh16, HeadMove.apply]
  · intro j
    have hv : (tengSlot e ⟨j.val, by omega⟩).val = if j.val = 32 then 62 else 66 + j.val := by
      simp [tengSlot, tengSlotVal, show j.val < 34 from j.isLt]
    refine ⟨(far j).1, (hH _ (by rw [hv]; split_ifs <;> omega) (by rw [hv]; split_ifs <;> omega)
      (by rw [hv]; split_ifs <;> omega)).trans (far j).2⟩

end Stage3

end
end NearCubicWires.PacketsCombine

import Proof.Packets.PacketsLowerCore

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.LowerCore
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
noncomputable section

/-- The arena tape of arena index `i`. -/
def arenaTape (i : Fin 34) : Fin 302 := kbSlots (KitBoot.outSlot i)

theorem arenaTape_val (i : Fin 34) : (arenaTape i).val = if i.val = 32 then 174 else 178 + i.val := by
  unfold arenaTape KitBoot.outSlot
  rw [kbSlots_val, KitBoot.arenaSlots_val]
  simp only [Fin.val_castAdd]
  split_ifs <;> omega

section Facts
variable (Rb C w pop cap : ℕ) (input reg cw : List Bool)

def Facts1 (H : Fin 302 → ℕ) (A : Fin 302 → List Bool) : Prop :=
  A 0 = input ∧ H 0 = 0 ∧ A 1 = ZeroPadding.pad Rb reg ∧ H 1 = 0 ∧ A 2 = ZeroPadding.pad Rb [] ∧ H 2 = 0 ∧
  A 3 = ZeroPadding.pad Rb (UnaryTemplate.tape C) ∧ H 3 = 0 ∧
  A 4 = ZeroPadding.pad Rb (UnaryTemplate.tape C) ∧ H 4 = 0 ∧
  A 5 = ZeroPadding.pad Rb (UnaryTemplate.tape w) ∧ H 5 = 0 ∧
  A 6 = ZeroPadding.pad Rb (UnaryTemplate.tape pop) ∧ H 6 = 0 ∧
  A 7 = ZeroPadding.pad Rb (List.replicate cap true) ∧ H 7 = 0 ∧
  A 8 = ZeroPadding.pad Rb cw ∧ H 8 = 0 ∧
  ∀ i : Fin 302, 130 ≤ i.val → A i = ZeroPadding.pad Rb [] ∧ H i = 0

def Facts2 (H : Fin 302 → ℕ) (A : Fin 302 → List Bool) : Prop :=
  A 0 = input ∧ H 0 = 0 ∧ A 1 = ZeroPadding.pad Rb reg ∧ H 1 = 0 ∧ A 2 = ZeroPadding.pad Rb [] ∧ H 2 = 0 ∧
  A 6 = ZeroPadding.pad Rb (UnaryTemplate.tape pop) ∧ H 6 = 0 ∧
  A 7 = ZeroPadding.pad Rb (List.replicate cap true) ∧ H 7 = 0 ∧
  A 8 = ZeroPadding.pad Rb cw ∧ H 8 = 0 ∧
  (∀ i : Fin 34, A (arenaTape i) = ZeroPadding.pad Rb (ReusableArithmetic.state C (PolyKit.reserve C w) [] [] i) ∧
    H (arenaTape i) = ReusableArithmetic.heads i) ∧
  ∀ i : Fin 302, 224 ≤ i.val → A i = ZeroPadding.pad Rb [] ∧ H i = 0

end Facts

/-! ## Stage 1: the metadata -/

/-! ## Stage 2: the arena -/

theorem kb_slot_small (k : Fin 97) (hk : k.val < 3) : (kbSlots k).val = 3 + k.val := by
  rw [kbSlots_val]; simp [hk]
theorem kb_slot_big (k : Fin 97) (hk : ¬ k.val < 3) : (kbSlots k).val = 127 + k.val := by
  rw [kbSlots_val]; simp [hk]

theorem stage2 (Rb C w pop cap : ℕ) (input reg cw : List Bool) (H : Fin 302 → ℕ) (A : Fin 302 → List Bool)
    (f : Facts1 Rb C w pop cap input reg cw H A) :
    ∃ (H' : Fin 302 → ℕ) (A' : Fin 302 → List Bool), Step kbStep (KitBoot.cost C w) H A H' A' ∧
      Facts2 Rb C w pop cap input reg cw H' A' := by
  obtain ⟨fa0, fh0, fa1, fh1, fa2, fh2, fa3, fh3, fa4, fh4, fa5, fh5, fa6, fh6, fa7, fh7, fa8, fh8, ffree⟩ := f
  obtain ⟨kH, kA, ks, kout⟩ := KitBoot.run C w
  obtain ⟨H', A', st, o, kp⟩ := Dock.lift ks kbSlots kbSlots_injective (fun _ => Rb) H A (by
    intro k
    by_cases hk : k.val < 3
    · have hv := kb_slot_small k hk
      have hk3 : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by omega
      rcases hk3 with h | h | h
      · have e : kbSlots k = 3 := Fin.ext (by rw [hv, h]; rfl)
        rw [e, fa3, fh3]; refine ⟨rfl, ?_⟩; unfold KitBoot.entry; simp [h]
      · have e : kbSlots k = 4 := Fin.ext (by rw [hv, h]; rfl)
        rw [e, fa4, fh4]; refine ⟨rfl, ?_⟩; unfold KitBoot.entry; simp [h]
      · have e : kbSlots k = 5 := Fin.ext (by rw [hv, h]; rfl)
        rw [e, fa5, fh5]; refine ⟨rfl, ?_⟩; unfold KitBoot.entry; simp [h]
    · have hv := kb_slot_big k hk
      rw [(ffree _ (by omega)).1, (ffree _ (by omega)).2, KitBoot.entry_high C w k (by omega)]
      exact ⟨rfl, rfl⟩)
  have keep : ∀ i : Fin 302, (i.val < 3 ∨ (5 < i.val ∧ i.val < 130) ∨ 223 < i.val) → A' i = A i ∧ H' i = H i := by
    intro i hi
    have := kp i (kbSlots_ne i hi)
    exact ⟨this.2, this.1⟩
  refine ⟨H', A', st, ?_⟩
  refine ⟨(keep 0 (by simp)).1.trans fa0, (keep 0 (by simp)).2.trans fh0, (keep 1 (by simp)).1.trans fa1,
    (keep 1 (by simp)).2.trans fh1, (keep 2 (by simp)).1.trans fa2, (keep 2 (by simp)).2.trans fh2,
    (keep 6 (by simp)).1.trans fa6, (keep 6 (by simp)).2.trans fh6, (keep 7 (by simp)).1.trans fa7,
    (keep 7 (by simp)).2.trans fh7, (keep 8 (by simp)).1.trans fa8, (keep 8 (by simp)).2.trans fh8, ?_, ?_⟩
  · intro i
    have hi := o (KitBoot.outSlot i)
    have hk := kout i
    unfold arenaTape
    rw [hi.1, hi.2, hk.1, hk.2]
    exact ⟨rfl, rfl⟩
  · intro i hi
    rw [(keep i (by omega)).1, (keep i (by omega)).2]
    exact ffree i (by omega)

def Facts3 (Rb C w pop : ℕ) (input reg cache : List Bool) (H : Fin 302 → ℕ) (A : Fin 302 → List Bool) : Prop :=
  A 0 = input ∧ H 0 = 0 ∧ A 1 = ZeroPadding.pad Rb reg ∧ H 1 = 0 ∧ A 2 = ZeroPadding.pad Rb [] ∧ H 2 = 0 ∧
  A 6 = ZeroPadding.pad Rb (UnaryTemplate.tape pop) ∧ H 6 = 0 ∧
  (∀ i : Fin 34, A (arenaTape i) = ZeroPadding.pad Rb (ReusableArithmetic.state C (PolyKit.reserve C w) [] [] i) ∧
    H (arenaTape i) = ReusableArithmetic.heads i) ∧
  A 278 = ZeroPadding.pad Rb cache ∧ H 278 = 0 ∧
  ∀ i : Fin 302, 242 ≤ i.val → i.val ≠ 278 → A i = ZeroPadding.pad Rb [] ∧ H i = 0

theorem ra_val (k : Fin 17) : (raSlots (Fin.castAdd 1 k)).val =
    if k.val = 0 then 8 else if k.val = 15 then 7 else if k.val = 12 then 278 else 224 + k.val := by
  rw [raSlots_val]; simp only [Fin.val_castAdd]

theorem start_data_blank (Rb cap : ℕ) (source : List Bool) (k : Fin 17) (h0 : k.val ≠ 0) (h15 : k.val ≠ 15)
    (hcap : cap + 1 ≤ Rb) :
    ZeroPadding.pad Rb (CloseoutRowsRawAtomStart.data cap source [] k) = ZeroPadding.pad Rb [] := by
  unfold CloseoutRowsRawAtomStart.data CloseoutRowsRawAtomReuse.data
  have e0 : ¬ k = 0 := fun h => h0 (by rw [h]; rfl)
  have e15 : ¬ k = 15 := fun h => h15 (by rw [h]; rfl)
  by_cases h1113 : k = 11 ∨ k = 13
  · rw [if_pos h1113]
  · rw [if_neg h1113]
    have e11 : ¬ k = 11 := fun h => h1113 (Or.inl h)
    have e13 : ¬ k = 13 := fun h => h1113 (Or.inr h)
    simp only [e0, e11, e13, e15, if_false]
    by_cases h12 : k = 12
    · rw [if_pos h12]
    · rw [if_neg h12]
      by_cases h16 : k = 16
      · rw [if_pos h16]; exact Dock.pad_zeros Rb (cap + 1) hcap
      · rw [if_neg h16]; exact Dock.pad_zeros Rb cap (by omega)

theorem stage3 {q : ℕ} (a : DecompositionAlgorithm) (occ : List (SupplierPipeline.SupportedNormalizedGate q))
    (Rb C w pop cap : ℕ) (input reg : List Bool) (H : Fin 302 → ℕ) (A : Fin 302 → List Bool)
    (hc : 64 * (ExtDecompositionBatch.B a occ + 2) ^ 2 ≤ cap) (hcapRb : cap + 1 ≤ Rb)
    (hlog : CloseoutRowsRawAtomProducer.budget cap occ.length ≤ Rb)
    (f : Facts2 Rb C w pop cap input reg (CloseoutRowsRawAtomMeaning.countWord a occ) H A) :
    ∃ (H' : Fin 302 → ℕ) (A' : Fin 302 → List Bool),
      Step raStep (2 * CloseoutRowsRawAtomProducer.budget cap occ.length + 2) H A H' A' ∧
      Facts3 Rb C w pop input reg (CloseoutRowsRawAtomBatch.atoms 0 (ExtDecompositionBatch.counts a occ)) H' A' := by
  obtain ⟨fa0, fh0, fa1, fh1, fa2, fh2, fa6, fh6, fa7, fh7, fa8, fh8, farena, ffree⟩ := f
  have raw : Step CloseoutRowsRawAtomProducer.machine (CloseoutRowsRawAtomProducer.budget cap occ.length)
      (CloseoutRowsRawAtomStart.heads [])
      (CloseoutRowsRawAtomStart.data cap (CloseoutRowsRawAtomMeaning.countWord a occ) [])
      (CloseoutRowsRawAtomReuse.heads (CloseoutRowsRawAtomMeaning.countWord a occ).length
        (ExtDecompositionBatch.B a occ) ([] ++ CloseoutRowsRawAtomBatch.atoms 0 (ExtDecompositionBatch.counts a occ)))
      (CloseoutRowsRawAtomReuse.data cap (CloseoutRowsRawAtomMeaning.countWord a occ)
        (ExtDecompositionBatch.B a occ) (ExtDecompositionBatch.B a occ)
        ([] ++ CloseoutRowsRawAtomBatch.atoms 0 (ExtDecompositionBatch.counts a occ))) := by
    obtain ⟨r, hr, hh, ht, hs⟩ := CloseoutRowsRawAtomProducer.source_run a occ cap [] hc
    exact ⟨r, hr, hh, ht, hs⟩
  have masked := raw.mask rawSel (by intro i _; simp [CloseoutRowsRawAtomStart.heads]) le_rfl
  obtain ⟨H', A', st, o, kp⟩ := Dock.lift masked raSlots raSlots_injective (fun _ => Rb) H A (by
    intro k
    refine Fin.addCases (fun k' => ?_) (fun e => ?_) k
    · simp only [Fin.addCases_left]
      have hv := ra_val k'
      by_cases h0 : k'.val = 0
      · have e : raSlots (Fin.castAdd 1 k') = 8 := Fin.ext (by rw [hv]; simp [h0])
        rw [e, fa8, fh8]
        refine ⟨by simp [CloseoutRowsRawAtomStart.heads], ?_⟩
        have hk : k' = 0 := Fin.ext h0
        rw [hk]; rfl
      by_cases h15 : k'.val = 15
      · have e : raSlots (Fin.castAdd 1 k') = 7 := Fin.ext (by rw [hv]; simp [h15])
        rw [e, fa7, fh7]
        refine ⟨by simp [CloseoutRowsRawAtomStart.heads], ?_⟩
        have hk : k' = 15 := Fin.ext h15
        rw [hk]; rfl
      · have hbig : 224 ≤ (raSlots (Fin.castAdd 1 k')).val := by rw [hv]; split_ifs <;> omega
        rw [(ffree _ hbig).1, (ffree _ hbig).2, start_data_blank Rb cap _ k' h0 h15 hcapRb]
        exact ⟨by simp [CloseoutRowsRawAtomStart.heads], rfl⟩
    · simp only [Fin.addCases_right]
      have hbig : 224 ≤ (raSlots (Fin.natAdd 17 e)).val := by rw [raSlots_val]; simp
      rw [(ffree _ hbig).1, (ffree _ hbig).2, Dock.pad_zeros Rb _ hlog]
      exact ⟨rfl, rfl⟩)
  have keep : ∀ i : Fin 302, (i.val ≠ 7 ∧ i.val ≠ 8 ∧ i.val ≠ 278 ∧ (i.val < 224 ∨ 241 < i.val)) →
      A' i = A i ∧ H' i = H i := by
    intro i hi
    have := kp i (raSlots_ne i hi)
    exact ⟨this.2, this.1⟩
  have e278 : raSlots (Fin.castAdd 1 12) = 278 := Fin.ext (by rw [ra_val]; rfl)
  have o278 := o (Fin.castAdd 1 12)
  rw [e278] at o278
  simp only [Fin.addCases_left] at o278
  refine ⟨H', A', st, (keep 0 (by simp)).1.trans fa0, (keep 0 (by simp)).2.trans fh0,
    (keep 1 (by simp)).1.trans fa1, (keep 1 (by simp)).2.trans fh1, (keep 2 (by simp)).1.trans fa2,
    (keep 2 (by simp)).2.trans fh2, (keep 6 (by simp)).1.trans fa6, (keep 6 (by simp)).2.trans fh6, ?_, ?_, ?_, ?_⟩
  · intro i
    have hv := arenaTape_val i
    have hk := keep (arenaTape i) (by split_ifs at hv <;> omega)
    rw [hk.1, hk.2]
    exact farena i
  · rw [o278.2]; rfl
  · rw [o278.1]; simp [rawSel]
  · intro i hi h278
    rw [(keep i (by omega)).1, (keep i (by omega)).2]
    exact ffree i (by omega)

end
end NearCubicWires.PacketsConstruction.LowerCore

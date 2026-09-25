import Proof.Packets.PacketsCoordInput

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.Residual
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
noncomputable section

/-- The exact frame-form lift (`Dock.lift` at cap `0`). -/
theorem liftExact {t u s n : ℕ} {p : Machine t s} {h0 h1 : Fin t → ℕ} {a0 a1 : Fin t → List Bool}
    (run : Step p n h0 a0 h1 a1) (σ : Fin t → Fin u) (hσ : Function.Injective σ) (H : Fin u → ℕ)
    (A : Fin u → List Bool) (hin : ∀ l, H (σ l) = h0 l ∧ A (σ l) = a0 l) :
    ∃ (H' : Fin u → ℕ) (A' : Fin u → List Bool), Step (RecoveryFocus.machine σ p) n H A H' A' ∧
      (∀ l, H' (σ l) = h1 l ∧ A' (σ l) = a1 l) ∧ (∀ i, (∀ l, σ l ≠ i) → H' i = H i ∧ A' i = A i) := by
  obtain ⟨H', A', st, hs, ho⟩ := Dock.lift run σ hσ (fun _ => 0) H A
    (fun l => ⟨(hin l).1, by rw [ZeroPadding.pad_zero]; exact (hin l).2⟩)
  exact ⟨H', A', st, fun l => ⟨(hs l).1, by rw [(hs l).2, ZeroPadding.pad_zero]⟩, ho⟩

section Mid
variable (a : DecompositionAlgorithm) (K : KitShape a) (r : Request) (k : rcKey a r) (j : ℕ)

/-- Region tape `10 + v` once the slots `W` are written. -/
def regionWord (W : ℕ → Bool) (v : ℕ) : List Bool :=
  if W v then allTable (K.C r) (K.w r) (rootOf a r) (popOf a r) (Bof a r) (nOf a r) ((maskBitsList a r k).getD j [])
    (startXOf a r k) (startYOf a r k) (labelsOf a r k) v else []

/-- The middle bank's invariant during preparation. -/
structure MidInv (Tm : ℕ) (W : ℕ → Bool) (P : ℕ) (H : Fin Tm → ℕ) (A : Fin Tm → List Bool) : Prop where
  key : ∀ i : Fin Tm, i.val < 10 → A i = keyEntry a r k j Tm i ∧ H i = 0
  region : ∀ i : Fin Tm, 10 ≤ i.val → i.val < 752 → A i = regionWord a K r k j W (i.val - 10) ∧ H i = 0
  fresh : ∀ i : Fin Tm, P ≤ i.val → A i = [] ∧ H i = 0

/-- The initial middle bank satisfies the invariant with nothing written. -/
theorem midInv_init (Tm : ℕ) : MidInv a K r k j Tm (fun _ => false) 752 (fun _ => 0) (keyEntry a r k j Tm) where
  key := fun _ _ => ⟨rfl, rfl⟩
  region := fun i h10 _ => by
    refine ⟨?_, rfl⟩
    simp only [regionWord, Bool.false_eq_true, if_false, keyEntry, PacketsCombine.metaEntry]
    rw [if_neg (by omega), if_neg (by omega), dif_neg (by omega)]
  fresh := fun i hP => by
    refine ⟨?_, rfl⟩
    simp only [keyEntry, PacketsCombine.metaEntry]
    rw [if_neg (by omega), if_neg (by omega), dif_neg (by omega)]

/-- **The generic preparation step.** -/
theorem inv_step {Tm t s n : ℕ} {p : Machine t s} {h0 h1 : Fin t → ℕ} {a0 a1 : Fin t → List Bool}
    (run : Step p n h0 a0 h1 a1) (σ : Fin t → Fin Tm) (hσ : Function.Injective σ) (W W' : ℕ → Bool)
    (P P' : ℕ) (hP : 752 ≤ P) (hPP : P ≤ P') (hW : ∀ v, W v = true → W' v = true)
    (hkey : ∀ l, (σ l).val < 10 → a0 l = keyEntry a r k j Tm (σ l) ∧ h0 l = 0 ∧ a1 l = a0 l ∧ h1 l = 0)
    (hout : ∀ l, 10 ≤ (σ l).val → (σ l).val < 752 → W ((σ l).val - 10) = false ∧ a0 l = [] ∧ h0 l = 0 ∧
      a1 l = regionWord a K r k j W' ((σ l).val - 10) ∧ h1 l = 0)
    (hpriv : ∀ l, 752 ≤ (σ l).val → P ≤ (σ l).val ∧ (σ l).val < P' ∧ a0 l = [] ∧ h0 l = 0)
    (hnew : ∀ v, v < 742 → W' v = true → W v = false → ∃ l, (σ l).val = 10 + v)
    (H : Fin Tm → ℕ) (A : Fin Tm → List Bool) (hI : MidInv a K r k j Tm W P H A) :
    ∃ (H' : Fin Tm → ℕ) (A' : Fin Tm → List Bool), Step (RecoveryFocus.machine σ p) n H A H' A' ∧
      MidInv a K r k j Tm W' P' H' A' := by
  obtain ⟨H', A', st, hs, ho⟩ := liftExact run σ hσ H A (by
    intro l
    by_cases h10 : (σ l).val < 10
    · obtain ⟨e0, e1, _, _⟩ := hkey l h10
      exact ⟨by rw [(hI.key _ h10).2, e1], by rw [(hI.key _ h10).1, e0]⟩
    · by_cases h752 : (σ l).val < 752
      · obtain ⟨hw, e0, e1, _, _⟩ := hout l (by omega) h752
        have hr := hI.region _ (by omega) h752
        refine ⟨by rw [hr.2, e1], ?_⟩
        rw [hr.1, e0]
        simp [regionWord, hw]
      · obtain ⟨hp, _, e0, e1⟩ := hpriv l (by omega)
        have hf := hI.fresh _ hp
        exact ⟨by rw [hf.2, e1], by rw [hf.1, e0]⟩)
  refine ⟨H', A', st, ⟨?_, ?_, ?_⟩⟩
  · intro i hi
    by_cases hsl : ∃ l, σ l = i
    · obtain ⟨l, rfl⟩ := hsl
      obtain ⟨e0, _, e2, e3⟩ := hkey l hi
      rw [(hs l).2, (hs l).1, e2, e0, e3]
      exact ⟨rfl, rfl⟩
    · simp only [not_exists] at hsl
      rw [(ho i hsl).1, (ho i hsl).2]
      exact hI.key i hi
  · intro i h10 h752
    by_cases hsl : ∃ l, σ l = i
    · obtain ⟨l, rfl⟩ := hsl
      obtain ⟨_, _, _, e2, e3⟩ := hout l h10 h752
      rw [(hs l).2, (hs l).1, e2, e3]
      exact ⟨rfl, rfl⟩
    · simp only [not_exists] at hsl
      rw [(ho i hsl).1, (ho i hsl).2]
      refine ⟨?_, (hI.region i h10 h752).2⟩
      rw [(hI.region i h10 h752).1]
      unfold regionWord
      by_cases hwv : W (i.val - 10) = true
      · rw [if_pos hwv, if_pos (hW _ hwv)]
      · have hwv' : W (i.val - 10) = false := by simpa using hwv
        rw [if_neg hwv]
        by_cases hw' : W' (i.val - 10) = true
        · obtain ⟨l, hl⟩ := hnew (i.val - 10) (by omega) hw' hwv'
          exact absurd (Fin.ext (by rw [hl]; omega)) (hsl l)
        · rw [if_neg hw']
  · intro i hi
    have hsl : ∀ l, σ l ≠ i := by
      intro l hl
      by_cases h10 : (σ l).val < 10
      · rw [hl] at h10; omega
      · by_cases h752 : (σ l).val < 752
        · rw [hl] at h752; omega
        · have := (hpriv l (by omega)).2.1
          rw [hl] at this; omega
    rw [(ho i hsl).1, (ho i hsl).2]
    exact hI.fresh i (by omega)

/-! ## Instances: key-level words and key-and-mask-level words -/

/-- A key word's slots: `l < 9 ↦ l`, `9 ↦ o`, private `10 + e ↦ p + e`. -/
def kwSlot (Tm o p e : ℕ) (ho : o < Tm) (hp : p + e ≤ Tm) (h9 : 9 < Tm) (l : Fin (10 + e)) : Fin Tm :=
  ⟨if l.val < 9 then l.val else if l.val = 9 then o else p + (l.val - 10), by
    have := l.isLt; split_ifs <;> omega⟩

theorem kwSlot_val (Tm o p e : ℕ) (ho : o < Tm) (hp : p + e ≤ Tm) (h9 : 9 < Tm) (l : Fin (10 + e)) :
    (kwSlot Tm o p e ho hp h9 l).val = if l.val < 9 then l.val else if l.val = 9 then o else p + (l.val - 10) := rfl

/-- **One key word written on region slot `o`** (private tapes at `[p, p + extra)`). -/
theorem kw_step {v : ∀ r : Request, rcKey a r → List Bool} (st : KeyWord a v) (hk : k ∈ rcKeys a r)
    (Tm o p : ℕ) (ho10 : 10 ≤ o) (ho : o < 752) (hp : 752 ≤ p) (hTm : p + st.extra ≤ Tm)
    (W : ℕ → Bool) (hWo : W (o - 10) = false)
    (hval : v r k = allTable (K.C r) (K.w r) (rootOf a r) (popOf a r) (Bof a r) (nOf a r)
      ((maskBitsList a r k).getD j []) (startXOf a r k) (startYOf a r k) (labelsOf a r k) (o - 10))
    (H : Fin Tm → ℕ) (A : Fin Tm → List Bool) (hI : MidInv a K r k j Tm W p H A) :
    ∃ (H' : Fin Tm → ℕ) (A' : Fin Tm → List Bool),
      Step (RecoveryFocus.machine (kwSlot Tm o p st.extra (by omega) hTm (by omega)) st.machine) (st.cost r)
        H A H' A' ∧
      MidInv a K r k j Tm (fun u => W u || u == o - 10) (p + st.extra) H' A' := by
  obtain ⟨H1, A1, hs, hkeep, h9A, h9H⟩ := st.run r k hk
  have h9lt : 9 < 10 + st.extra := by omega
  have hinj : Function.Injective (kwSlot Tm o p st.extra (by omega) hTm (by omega)) := by
    intro x y h
    have hv := congrArg Fin.val h
    rw [kwSlot_val, kwSlot_val] at hv
    apply Fin.ext
    split_ifs at hv <;> omega
  refine inv_step a K r k j hs _ hinj W _ p (p + st.extra) hp (by omega)
    (fun u hu => by simp [hu]) ?_ ?_ ?_ ?_ H A hI
  · intro l hl
    have hl9 : l.val < 9 := by
      by_contra hc
      rw [kwSlot_val, if_neg hc] at hl
      by_cases h9 : l.val = 9
      · rw [if_pos h9] at hl; omega
      · rw [if_neg h9] at hl; omega
    have hk' := hkeep l hl9
    refine ⟨?_, rfl, hk'.1, hk'.2⟩
    have hv : (kwSlot Tm o p st.extra (by omega) hTm (by omega) l).val = l.val := by
      rw [kwSlot_val, if_pos hl9]
    simp only [keyEntry, PacketsCombine.metaEntry, hv]
    rw [if_neg (show ¬ (l.val = 9) by omega)]
  · intro l h10 h752
    have hl9 : l.val = 9 := by
      by_contra hc
      have hlt : ¬ (l.val < 9) := fun h => by rw [kwSlot_val, if_pos h] at h10; omega
      rw [kwSlot_val, if_neg hlt, if_neg hc] at h752
      omega
    have hv : (kwSlot Tm o p st.extra (by omega) hTm (by omega) l).val = o := by
      rw [kwSlot_val, if_neg (by omega), if_pos hl9]
    rw [show l = ⟨9, h9lt⟩ from Fin.ext hl9] at hv ⊢
    refine ⟨by rw [hv]; exact hWo, ?_, rfl, ?_, h9H⟩
    · simp [PacketsCombine.metaEntry]
    · rw [h9A, hv, hval]
      simp [regionWord]
  · intro l h752
    have hl : 10 ≤ l.val := by
      by_contra hc
      by_cases h9 : l.val < 9
      · rw [kwSlot_val, if_pos h9] at h752; omega
      · have h9' : l.val = 9 := by omega
        rw [kwSlot_val, if_neg h9, if_pos h9'] at h752; omega
    rw [kwSlot_val] at h752 ⊢
    rw [if_neg (show ¬ (l.val < 9) by omega), if_neg (show ¬ (l.val = 9) by omega)] at h752 ⊢
    refine ⟨by omega, by have := l.isLt; omega, ?_, rfl⟩
    simp only [PacketsCombine.metaEntry]
    rw [if_neg (show ¬ (l.val = 0) by omega), dif_neg (show ¬ (1 ≤ l.val ∧ l.val ≤ 8) by omega)]
  · intro u _ hu hw
    simp only [Bool.or_eq_true, beq_iff_eq, hw, Bool.false_eq_true, false_or] at hu
    refine ⟨⟨9, h9lt⟩, ?_⟩
    rw [kwSlot_val]
    simp only [show ¬ (9 < 9) by omega, if_false, if_true]
    omega

/-- A key stage's slots: `l < 10 ↦ l`, `10 ↦ o`, private `11 + e ↦ p + e`. -/
def ksSlot (Tm o p e : ℕ) (ho : o < Tm) (hp : p + e ≤ Tm) (h9 : 9 < Tm) (l : Fin (11 + e)) : Fin Tm :=
  ⟨if l.val < 10 then l.val else if l.val = 10 then o else p + (l.val - 11), by
    have := l.isLt; split_ifs <;> omega⟩

theorem ksSlot_val (Tm o p e : ℕ) (ho : o < Tm) (hp : p + e ≤ Tm) (h9 : 9 < Tm) (l : Fin (11 + e)) :
    (ksSlot Tm o p e ho hp h9 l).val = if l.val < 10 then l.val else if l.val = 10 then o else p + (l.val - 11) :=
  rfl

/-- **One key-and-mask word written on region slot `o`.** -/
theorem ks_step {v : ∀ r : Request, rcKey a r → ℕ → List Bool} (st : KeyStage a v) (hk : k ∈ rcKeys a r)
    (hj : j < maskCount a r k)
    (Tm o p : ℕ) (ho10 : 10 ≤ o) (ho : o < 752) (hp : 752 ≤ p) (hTm : p + st.extra ≤ Tm)
    (W : ℕ → Bool) (hWo : W (o - 10) = false)
    (hval : v r k j = allTable (K.C r) (K.w r) (rootOf a r) (popOf a r) (Bof a r) (nOf a r)
      ((maskBitsList a r k).getD j []) (startXOf a r k) (startYOf a r k) (labelsOf a r k) (o - 10))
    (H : Fin Tm → ℕ) (A : Fin Tm → List Bool) (hI : MidInv a K r k j Tm W p H A) :
    ∃ (H' : Fin Tm → ℕ) (A' : Fin Tm → List Bool),
      Step (RecoveryFocus.machine (ksSlot Tm o p st.extra (by omega) hTm (by omega)) st.machine) (st.cost r)
        H A H' A' ∧
      MidInv a K r k j Tm (fun u => W u || u == o - 10) (p + st.extra) H' A' := by
  obtain ⟨H1, A1, hs, hkeep, h10A, h10H⟩ := st.run r k hk j hj
  have h10lt : 10 < 11 + st.extra := by omega
  have hinj : Function.Injective (ksSlot Tm o p st.extra (by omega) hTm (by omega)) := by
    intro x y h
    have hv := congrArg Fin.val h
    rw [ksSlot_val, ksSlot_val] at hv
    apply Fin.ext
    split_ifs at hv <;> omega
  refine inv_step a K r k j hs _ hinj W _ p (p + st.extra) hp (by omega)
    (fun u hu => by simp [hu]) ?_ ?_ ?_ ?_ H A hI
  · intro l hl
    have hl10 : l.val < 10 := by
      by_contra hc
      rw [ksSlot_val, if_neg hc] at hl
      by_cases h10 : l.val = 10
      · rw [if_pos h10] at hl; omega
      · rw [if_neg h10] at hl; omega
    have hk' := hkeep l hl10
    refine ⟨?_, rfl, hk'.1, hk'.2⟩
    have hv : (ksSlot Tm o p st.extra (by omega) hTm (by omega) l).val = l.val := by
      rw [ksSlot_val, if_pos hl10]
    simp only [keyEntry, PacketsCombine.metaEntry, hv]
  · intro l h10 h752
    have hl10 : l.val = 10 := by
      by_contra hc
      have hlt : ¬ (l.val < 10) := fun h => by rw [ksSlot_val, if_pos h] at h10; omega
      rw [ksSlot_val, if_neg hlt, if_neg hc] at h752
      omega
    have hv : (ksSlot Tm o p st.extra (by omega) hTm (by omega) l).val = o := by
      rw [ksSlot_val, if_neg (by omega), if_pos hl10]
    rw [show l = ⟨10, h10lt⟩ from Fin.ext hl10] at hv ⊢
    refine ⟨by rw [hv]; exact hWo, ?_, rfl, ?_, h10H⟩
    · simp [keyEntry, PacketsCombine.metaEntry]
    · rw [h10A, hv, hval]
      simp [regionWord]
  · intro l h752
    have hl : 11 ≤ l.val := by
      by_contra hc
      by_cases h9 : l.val < 10
      · rw [ksSlot_val, if_pos h9] at h752; omega
      · have h9' : l.val = 10 := by omega
        rw [ksSlot_val, if_neg h9, if_pos h9'] at h752; omega
    rw [ksSlot_val] at h752 ⊢
    rw [if_neg (show ¬ (l.val < 10) by omega), if_neg (show ¬ (l.val = 10) by omega)] at h752 ⊢
    refine ⟨by omega, by have := l.isLt; omega, ?_, rfl⟩
    simp only [keyEntry, PacketsCombine.metaEntry]
    rw [if_neg (show ¬ (l.val = 9) by omega), if_neg (show ¬ (l.val = 0) by omega),
      dif_neg (show ¬ (1 ≤ l.val ∧ l.val ≤ 8) by omega)]
  · intro u _ hu hw
    simp only [Bool.or_eq_true, beq_iff_eq, hw, Bool.false_eq_true, false_or] at hu
    refine ⟨⟨10, h10lt⟩, ?_⟩
    rw [ksSlot_val]
    simp only [show ¬ (10 < 10) by omega, if_false, if_true]
    omega

end Mid

end
end NearCubicWires.PacketsConstruction.Residual

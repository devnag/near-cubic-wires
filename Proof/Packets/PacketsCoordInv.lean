import Proof.Packets.PacketsCoordBudget

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.Residual.Donor
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
noncomputable section

/-- The port words (`W`: which of the four written ports 10, 12, 14, 15 already hold their value). -/
def portWord (W : ℕ → Bool) (mode : Bool) (L R Llog cap M : ℕ) (i : ℕ) : List Bool :=
  if i = 10 then (if W 10 then [mode] else [])
  else if i = 12 then (if W 12 then List.replicate L true else [])
  else if i = 13 then List.replicate Llog false
  else if i = 14 then (if W 14 then List.replicate R true else [])
  else if i = 15 then (if W 15 then CompareMachine.word M else [])
  else if i = 16 then List.replicate cap false
  else []

section Inv
variable (a : DecompositionAlgorithm) (r : Request) (k : rcKey a r) (T S : ℕ) (mode : Bool) (L R Llog cap M : ℕ)

def dEntry (i : Fin T) : List Bool :=
  if i.val < 9 then PacketsCombine.metaEntry a r (some k) T i
  else if i.val < 17 then portWord (fun _ => false) mode L R Llog cap M i.val
  else if i.val < S then List.replicate R false else []

structure DInv (W : ℕ → Bool) (P : ℕ) (H : Fin T → ℕ) (A : Fin T → List Bool) : Prop where
  key : ∀ i : Fin T, i.val < 9 → A i = PacketsCombine.metaEntry a r (some k) T i ∧ H i = 0
  port : ∀ i : Fin T, 9 ≤ i.val → i.val < 17 → A i = portWord W mode L R Llog cap M i.val ∧ H i = 0
  scratch : ∀ i : Fin T, 17 ≤ i.val → i.val < S → A i = List.replicate R false ∧ H i = 0
  fresh : ∀ i : Fin T, P ≤ i.val → A i = [] ∧ H i = 0

theorem dInv_init (hS : 17 ≤ S) :
    DInv a r k T S mode L R Llog cap M (fun _ => false) S (fun _ => 0) (dEntry a r k T S mode L R Llog cap M) where
  key := fun i hi => ⟨by simp only [dEntry, if_pos hi], rfl⟩
  port := fun i h9 h17 => ⟨by simp only [dEntry, if_neg (show ¬ (i.val < 9) by omega), if_pos h17], rfl⟩
  scratch := fun i h17 hS' => ⟨by
    simp only [dEntry, if_neg (show ¬ (i.val < 9) by omega), if_neg (show ¬ (i.val < 17) by omega), if_pos hS'], rfl⟩
  fresh := fun i hP => ⟨by
    simp only [dEntry, if_neg (show ¬ (i.val < 9) by omega), if_neg (show ¬ (i.val < 17) by omega),
      if_neg (show ¬ (i.val < S) by omega)], rfl⟩

/-- **The generic docked pre-phase step.** -/
theorem dinv_step {t s n : ℕ} {p : Machine t s} {h0 h1 : Fin t → ℕ} {a0 a1 : Fin t → List Bool}
    (run : Step p n h0 a0 h1 a1) (σ : Fin t → Fin T) (hσ : Function.Injective σ) (W W' : ℕ → Bool)
    (P P' : ℕ) (hS17 : 17 ≤ S) (hSP : S ≤ P) (hPP : P ≤ P')
    (hkey : ∀ l, (σ l).val < 9 → a0 l = PacketsCombine.metaEntry a r (some k) T (σ l) ∧ h0 l = 0 ∧
      a1 l = a0 l ∧ h1 l = 0)
    (hout : ∀ l, 9 ≤ (σ l).val → (σ l).val < 17 → a0 l = portWord W mode L R Llog cap M (σ l).val ∧ h0 l = 0 ∧
      a1 l = portWord W' mode L R Llog cap M (σ l).val ∧ h1 l = 0)
    (hpriv : ∀ l, 17 ≤ (σ l).val → P ≤ (σ l).val ∧ (σ l).val < P' ∧ a0 l = [] ∧ h0 l = 0)
    (hW : ∀ i, 9 ≤ i → i < 17 → (∀ l, (σ l).val ≠ i) →
      portWord W' mode L R Llog cap M i = portWord W mode L R Llog cap M i)
    (H : Fin T → ℕ) (A : Fin T → List Bool) (hI : DInv a r k T S mode L R Llog cap M W P H A) :
    ∃ (H' : Fin T → ℕ) (A' : Fin T → List Bool), Step (RecoveryFocus.machine σ p) n H A H' A' ∧
      DInv a r k T S mode L R Llog cap M W' P' H' A' := by
  obtain ⟨H', A', st, hs, ho⟩ := liftExact run σ hσ H A (by
    intro l
    by_cases h9 : (σ l).val < 9
    · obtain ⟨e0, e1, _, _⟩ := hkey l h9
      exact ⟨by rw [(hI.key _ h9).2, e1], by rw [(hI.key _ h9).1, e0]⟩
    · by_cases h17 : (σ l).val < 17
      · obtain ⟨e0, e1, _, _⟩ := hout l (by omega) h17
        have hr := hI.port _ (by omega) h17
        exact ⟨by rw [hr.2, e1], by rw [hr.1, e0]⟩
      · obtain ⟨hp, _, e0, e1⟩ := hpriv l (by omega)
        have hf := hI.fresh _ hp
        exact ⟨by rw [hf.2, e1], by rw [hf.1, e0]⟩)
  refine ⟨H', A', st, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro i hi
    by_cases hsl : ∃ l, σ l = i
    · obtain ⟨l, rfl⟩ := hsl
      obtain ⟨e0, _, e2, e3⟩ := hkey l hi
      rw [(hs l).2, (hs l).1, e2, e0, e3]
      exact ⟨rfl, rfl⟩
    · simp only [not_exists] at hsl
      rw [(ho i hsl).1, (ho i hsl).2]
      exact hI.key i hi
  · intro i h9 h17
    by_cases hsl : ∃ l, σ l = i
    · obtain ⟨l, rfl⟩ := hsl
      obtain ⟨_, _, e2, e3⟩ := hout l h9 h17
      rw [(hs l).2, (hs l).1, e2, e3]
      exact ⟨rfl, rfl⟩
    · simp only [not_exists] at hsl
      rw [(ho i hsl).1, (ho i hsl).2]
      refine ⟨?_, (hI.port i h9 h17).2⟩
      rw [(hI.port i h9 h17).1, hW i.val h9 h17 (fun l hl => hsl l (Fin.ext hl))]
  · intro i h17 hS'
    have hsl : ∀ l, σ l ≠ i := by
      intro l hl
      have := (hpriv l (by rw [hl]; exact h17)).1
      rw [hl] at this
      omega
    rw [(ho i hsl).1, (ho i hsl).2]
    exact hI.scratch i h17 hS'
  · intro i hi
    have hsl : ∀ l, σ l ≠ i := by
      intro l hl
      by_cases h9 : (σ l).val < 9
      · rw [hl] at h9; omega
      · by_cases h17 : (σ l).val < 17
        · rw [hl] at h17; omega
        · have := (hpriv l (by omega)).2.1
          rw [hl] at this; omega
    rw [(ho i hsl).1, (ho i hsl).2]
    exact hI.fresh i (by omega)

/-- **One key-level word written on port `o`** (one of the four written ports), private tapes at `[p, p + extra)`. -/
theorem dkw_step {v : ∀ r : Request, rcKey a r → List Bool} (st : KeyWord a v) (hk : k ∈ rcKeys a r)
    (o p : ℕ) (ho : o = 10 ∨ o = 12 ∨ o = 14 ∨ o = 15) (hSp : S ≤ p) (hS : 17 ≤ S) (hT : p + st.extra ≤ T)
    (W : ℕ → Bool) (hWo : W o = false)
    (hval : v r k = portWord (fun u => W u || u == o) mode L R Llog cap M o)
    (H : Fin T → ℕ) (A : Fin T → List Bool) (hI : DInv a r k T S mode L R Llog cap M W p H A) :
    ∃ (H' : Fin T → ℕ) (A' : Fin T → List Bool),
      Step (RecoveryFocus.machine (kwSlot T o p st.extra (by omega) hT (by omega)) st.machine) (st.cost r)
        H A H' A' ∧
      DInv a r k T S mode L R Llog cap M (fun u => W u || u == o) (p + st.extra) H' A' := by
  obtain ⟨H1, A1, hs, hkeep, h9A, h9H⟩ := st.run r k hk
  have h9lt : 9 < 10 + st.extra := by omega
  have hinj : Function.Injective (kwSlot T o p st.extra (by omega) hT (by omega)) := by
    intro x y h
    have hv := congrArg Fin.val h
    rw [kwSlot_val, kwSlot_val] at hv
    apply Fin.ext
    split_ifs at hv <;> omega
  refine dinv_step a r k T S mode L R Llog cap M hs _ hinj W _ p (p + st.extra) hS hSp (by omega) ?_ ?_ ?_ ?_ H A hI
  · intro l hl
    have hl9 : l.val < 9 := by
      by_contra hc
      rw [kwSlot_val, if_neg hc] at hl
      by_cases h9 : l.val = 9
      · rw [if_pos h9] at hl; omega
      · rw [if_neg h9] at hl; omega
    have hk' := hkeep l hl9
    refine ⟨?_, rfl, hk'.1, hk'.2⟩
    exact Residual.metaEntry_val r k _ _ _ _ (by rw [kwSlot_val, if_pos hl9])
  · intro l h9 h17
    have hl9 : l.val = 9 := by
      by_contra hc
      have hlt : ¬ (l.val < 9) := fun h => by rw [kwSlot_val, if_pos h] at h9; omega
      rw [kwSlot_val, if_neg hlt, if_neg hc] at h17
      omega
    have hv : (kwSlot T o p st.extra (by omega) hT (by omega) l).val = o := by
      rw [kwSlot_val, if_neg (by omega), if_pos hl9]
    rw [show l = ⟨9, h9lt⟩ from Fin.ext hl9] at hv ⊢
    rw [hv]
    refine ⟨?_, rfl, ?_, h9H⟩
    · simp only [PacketsCombine.metaEntry]
      rw [if_neg (show ¬ ((9 : ℕ) = 0) by omega), dif_neg (show ¬ (1 ≤ 9 ∧ 9 ≤ 8) by omega)]
      unfold portWord
      rcases ho with h | h | h | h <;> subst h <;> simp [hWo]
    · rw [h9A, hval]
  · intro l h17
    have hl : 10 ≤ l.val := by
      by_contra hc
      by_cases h9 : l.val < 9
      · rw [kwSlot_val, if_pos h9] at h17; omega
      · have h9' : l.val = 9 := by omega
        rw [kwSlot_val, if_neg h9, if_pos h9'] at h17; rcases ho with h | h | h | h <;> omega
    rw [kwSlot_val] at h17 ⊢
    rw [if_neg (show ¬ (l.val < 9) by omega), if_neg (show ¬ (l.val = 9) by omega)] at h17 ⊢
    refine ⟨by omega, by have := l.isLt; omega, ?_, rfl⟩
    simp only [PacketsCombine.metaEntry]
    rw [if_neg (show ¬ (l.val = 0) by omega), dif_neg (show ¬ (1 ≤ l.val ∧ l.val ≤ 8) by omega)]
  · intro i _ _ hn
    have hio : i ≠ o := by
      intro he
      apply hn ⟨9, h9lt⟩
      rw [kwSlot_val]
      simp only [show ¬ (9 < 9) by omega, if_false, if_true]
      exact he.symm
    have hb : ∀ u, u ≠ o → (W u || u == o) = W u := by
      intro u hu
      simp [hu]
    unfold portWord
    by_cases h10 : i = 10
    · subst h10; simp only [if_true, hb 10 hio]
    · by_cases h12 : i = 12
      · subst h12; simp only [if_neg h10, if_true, hb 12 hio]
      · by_cases h14 : i = 14
        · subst h14
          simp only [if_neg h10, if_neg h12, if_neg (show ¬ ((14 : ℕ) = 13) by omega), if_true, hb 14 hio]
        · by_cases h15 : i = 15
          · subst h15
            simp only [if_neg h10, if_neg h12, if_neg h14, if_neg (show ¬ ((15 : ℕ) = 13) by omega), if_true,
              hb 15 hio]
          · simp only [if_neg h10, if_neg h12, if_neg h14, if_neg h15]

end Inv

end
end NearCubicWires.PacketsConstruction.Residual.Donor

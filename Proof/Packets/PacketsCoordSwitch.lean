import Proof.Packets.PacketsCoordMid

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

variable {a : DecompositionAlgorithm}

theorem read_unary (B : ℕ) : readTapeBit (List.replicate B true) 0 = decide (1 ≤ B) := by
  cases B with
  | zero => rfl
  | succ n => simp [readTapeBit]

/-- The tape of the vector. -/
def MidParts.vecTape {K : KitShape a} (P : MidParts a K) : Fin P.Tm := ⟨714, by have := P.Tm_ge; omega⟩

/-- The terminal writer's slots (as in `termM`). -/
def MidParts.termSlot {K : KitShape a} (P : MidParts a K) : Fin (10 + P.termS.extra) → Fin P.Tm :=
  kwSlot P.Tm 714 P.b10 P.termS.extra (by have := P.Tm_ge; omega) (by unfold MidParts.Tm; omega)
    (by have := P.Tm_ge; omega)

theorem MidParts.termSlot_val {K : KitShape a} (P : MidParts a K) (l : Fin (10 + P.termS.extra)) :
    (P.termSlot l).val = if l.val < 9 then l.val else if l.val = 9 then 714 else P.b10 + (l.val - 10) := rfl

theorem MidParts.termSlot_injective {K : KitShape a} (P : MidParts a K) : Function.Injective P.termSlot := by
  have hb := P.bases
  intro x y h
  have hv := congrArg Fin.val h
  rw [P.termSlot_val, P.termSlot_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The `all_run` branch. -/
theorem mid_all {K : KitShape a} (P : MidParts a K) (hA : ConeBounds.RouteA a K) (r : Request) (k : rcKey a r)
    (hk : k ∈ rcKeys a r) (j : ℕ) (hj : j < maskCount a r k) (hB : 1 ≤ Bof a r)
    (H1 : Fin P.Tm → ℕ) (A1 : Fin P.Tm → List Bool)
    (hreg : ∀ i : Fin P.Tm, 10 ≤ i.val → i.val < 752 →
      A1 i = allTable (K.C r) (K.w r) (rootOf a r) (popOf a r) (Bof a r) (nOf a r) ((maskBitsList a r k).getD j [])
        (startXOf a r k) (startYOf a r k) (labelsOf a r k) (i.val - 10) ∧ H1 i = 0) :
    ∃ (H2 : Fin P.Tm → ℕ) (A2 : Fin P.Tm → List Bool),
      Step P.allM (ConeRun.budgetOf a K r k j) H1 A1 H2 A2 ∧
      (∀ i : Fin P.Tm, i.val < 10 → A2 i = A1 i ∧ H2 i = H1 i) ∧
      A2 P.vecTape = PolyKit.vector (K.C r) (K.w r) ((MaskCoord.maskCoordsList a r k).getD j []) := by
  refine (all_run_req a K hA r k hk hB j hj).elim fun Ha h1 => h1.elim fun Aa h2 => ?_
  have sa := h2.1
  have ha704 := h2.2
  refine (liftExact sa P.allSlot P.allSlot_injective H1 A1 (by
    intro i
    have h := hreg (P.allSlot i) (by show 10 ≤ 10 + i.val; omega) (by show 10 + i.val < 752; have := i.isLt; omega)
    refine ⟨h.2, ?_⟩
    rw [h.1]
    show allTable _ _ _ _ _ _ _ _ _ _ ((10 + i.val) - 10) = allTable _ _ _ _ _ _ _ _ _ _ i.val
    rw [Nat.add_sub_cancel_left])).elim fun H2 h3 => h3.elim fun A2 h4 => ?_
  have st := h4.1
  have hs := h4.2.1
  have ho := h4.2.2
  refine ⟨H2, A2, st, ?_, ?_⟩
  · intro i hi
    have hn : ∀ l, P.allSlot l ≠ i := by
      intro l hl
      have := congrArg Fin.val hl
      change 10 + l.val = i.val at this
      omega
    exact ⟨(ho i hn).2, (ho i hn).1⟩
  · have he : P.vecTape = P.allSlot 704 := Fin.ext rfl
    rw [he, (hs 704).2, ha704]

/-- The terminal branch. -/
theorem mid_term {K : KitShape a} (P : MidParts a K) (r : Request) (k : rcKey a r)
    (hk : k ∈ rcKeys a r) (j : ℕ) (hj : j < maskCount a r k) (hB0 : Bof a r = 0)
    (H1 : Fin P.Tm → ℕ) (A1 : Fin P.Tm → List Bool)
    (hkey : ∀ i : Fin P.Tm, i.val < 10 → A1 i = keyEntry a r k j P.Tm i ∧ H1 i = 0)
    (hreg : ∀ i : Fin P.Tm, 10 ≤ i.val → i.val < 752 →
      A1 i = allTable (K.C r) (K.w r) (rootOf a r) (popOf a r) (Bof a r) (nOf a r) ((maskBitsList a r k).getD j [])
        (startXOf a r k) (startYOf a r k) (labelsOf a r k) (i.val - 10) ∧ H1 i = 0)
    (hfresh : ∀ i : Fin P.Tm, P.b10 ≤ i.val → A1 i = [] ∧ H1 i = 0) :
    ∃ (H2 : Fin P.Tm → ℕ) (A2 : Fin P.Tm → List Bool),
      Step P.termM (P.termS.cost r) H1 A1 H2 A2 ∧
      (∀ i : Fin P.Tm, i.val < 10 → A2 i = A1 i ∧ H2 i = H1 i) ∧
      A2 P.vecTape = PolyKit.vector (K.C r) (K.w r) ((MaskCoord.maskCoordsList a r k).getD j []) := by
  have hb := P.bases
  obtain ⟨Ht, At, st0, hkeep, h9A, h9H⟩ := P.termS.run r k hk
  obtain ⟨H2, A2, st, hs, ho⟩ := liftExact st0 P.termSlot P.termSlot_injective H1 A1 (by
    intro l
    by_cases hl9 : l.val < 9
    · have hv : (P.termSlot l).val = l.val := by rw [P.termSlot_val, if_pos hl9]
      have h := hkey _ (by rw [hv]; omega)
      refine ⟨h.2, ?_⟩
      rw [h.1]
      simp only [keyEntry, PacketsCombine.metaEntry, hv]
      rw [if_neg (show ¬ (l.val = 9) by omega)]
    · by_cases hl : l.val = 9
      · have hv : (P.termSlot l).val = 714 := by rw [P.termSlot_val, if_neg hl9, if_pos hl]
        have h := hreg _ (by rw [hv]; omega) (by rw [hv]; omega)
        refine ⟨h.2, ?_⟩
        rw [h.1, hv]
        rw [allTable_other _ _ _ _ _ _ _ _ _ _ _ (by unfold slotSet; omega)]
        simp [PacketsCombine.metaEntry, hl]
      · have hv : (P.termSlot l).val = P.b10 + (l.val - 10) := by
          rw [P.termSlot_val, if_neg hl9, if_neg hl]
        have h := hfresh _ (by rw [hv]; omega)
        refine ⟨h.2, ?_⟩
        rw [h.1]
        simp only [PacketsCombine.metaEntry]
        rw [if_neg (show ¬ (l.val = 0) by omega), dif_neg (show ¬ (1 ≤ l.val ∧ l.val ≤ 8) by omega)])
  refine ⟨H2, A2, st, ?_, ?_⟩
  · intro i hi
    by_cases hsl : ∃ l, P.termSlot l = i
    · obtain ⟨l, hl⟩ := hsl
      have hl9 : l.val < 9 := by
        by_contra hc
        have hv := congrArg Fin.val hl
        rw [P.termSlot_val, if_neg hc] at hv
        split_ifs at hv <;> omega
      have hv : (P.termSlot l).val = l.val := by rw [P.termSlot_val, if_pos hl9]
      rw [← hl, (hs l).1, (hs l).2, (hkeep l hl9).1, (hkeep l hl9).2]
      have h := hkey (P.termSlot l) (by rw [hv]; omega)
      rw [h.1, h.2]
      refine ⟨?_, rfl⟩
      simp only [keyEntry, PacketsCombine.metaEntry, hv]
      rw [if_neg (show ¬ (l.val = 9) by omega)]
    · simp only [not_exists] at hsl
      exact ⟨(ho i hsl).2, (ho i hsl).1⟩
  · have he : P.vecTape = P.termSlot ⟨9, by omega⟩ := Fin.ext rfl
    rw [he, (hs _).2, h9A]
    have hj' : j < (MaskCoord.maskCoordsList a r k).length := hj
    have hz := ConeDegenerate.maskCoords_of_bound_zero a r k hB0 j hj'
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some, hz]
    rfl

/-- **Mask `j`'s vector on tape 714.** -/
theorem mid_run {K : KitShape a} (P : MidParts a K) (hA : ConeBounds.RouteA a K) (r : Request) (k : rcKey a r)
    (hk : k ∈ rcKeys a r) (j : ℕ) (hj : j < maskCount a r k) :
    ∃ (H : Fin P.Tm → ℕ) (A : Fin P.Tm → List Bool),
      Step P.midMachine (P.midCost r k j) (fun _ => 0) (keyEntry a r k j P.Tm) H A ∧
      (∀ i : Fin P.Tm, i.val < 10 → A i = keyEntry a r k j P.Tm i ∧ H i = 0) ∧
      A P.vecTape = PolyKit.vector (K.C r) (K.w r) ((MaskCoord.maskCoordsList a r k).getD j []) := by
  refine (prep_run P r k hk j hj).elim fun H1 h1 => h1.elim fun A1 h2 => ?_
  have sp := h2.1
  have hkey := h2.2.1
  have hreg := h2.2.2.1
  have hfresh := h2.2.2.2
  have hbt := hreg P.bTape (by show 10 ≤ 10; omega) (by show 10 < 752; omega)
  by_cases hB : 1 ≤ Bof a r
  · refine (mid_all P hA r k hk j hj hB H1 A1 hreg).elim fun H2 h3 => h3.elim fun A2 h4 => ?_
    have st := h4.1
    have hkept := h4.2.1
    have hvec := h4.2.2
    have hbit : readTapeBit (A1 P.bTape) (H1 P.bTape) = true := by
      rw [hbt.1, hbt.2]
      show readTapeBit (List.replicate (Bof a r) true) 0 = true
      rw [read_unary]
      exact decide_eq_true hB
    have sw := CloseoutRowsOriginalSwitch.true_run P.allM P.termM P.bTape st hbit
    refine ⟨H2, A2, (sp.seq sw).enlarge (by unfold MidParts.midCost; omega), ?_, hvec⟩
    intro i hi
    rw [(hkept i hi).1, (hkept i hi).2]
    exact hkey i hi
  · have hB0 : Bof a r = 0 := by omega
    refine (mid_term P r k hk j hj hB0 H1 A1 hkey hreg hfresh).elim fun H2 h3 => h3.elim fun A2 h4 => ?_
    have st := h4.1
    have hkept := h4.2.1
    have hvec := h4.2.2
    have hbit : readTapeBit (A1 P.bTape) (H1 P.bTape) = false := by
      rw [hbt.1, hbt.2]
      show readTapeBit (List.replicate (Bof a r) true) 0 = false
      rw [hB0]
      rfl
    have sw := CloseoutRowsOriginalSwitch.false_run P.allM P.termM P.bTape st hbit
    refine ⟨H2, A2, (sp.seq sw).enlarge (by unfold MidParts.midCost; omega), ?_, hvec⟩
    intro i hi
    rw [(hkept i hi).1, (hkept i hi).2]
    exact hkey i hi

end
end NearCubicWires.PacketsConstruction.Residual

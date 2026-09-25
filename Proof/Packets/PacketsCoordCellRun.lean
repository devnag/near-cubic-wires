import Proof.Packets.PacketsCoordCell

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

theorem metaEntry_val (r : Request) (k : rcKey a r) (t u : ℕ) (i : Fin t) (i' : Fin u) (h : i.val = i'.val) :
    PacketsCombine.metaEntry a r (some k) t i = PacketsCombine.metaEntry a r (some k) u i' := by
  unfold PacketsCombine.metaEntry
  simp only [h]

theorem cellHeads_σM {K : KitShape a} (C : CellParts a K) (out : List Bool) (i : Fin (C.mid.Tm + 1)) :
    C.cellHeads out (C.σM i) = 0 := by
  unfold CellParts.cellHeads
  rw [if_neg]
  rw [CellParts.σM_val]
  split_ifs <;> omega

theorem addCases_zero (n : ℕ) (i : Fin (n + 1)) :
    Fin.addCases (motive := fun _ => ℕ) (fun _ : Fin n => 0) (fun _ : Fin 1 => 0) i = 0 := by
  rw [addCases_val]; split_ifs <;> rfl

theorem cellBank_lo {K : KitShape a} (C : CellParts a K) (r : Request) (k : rcKey a r) (R L j : ℕ)
    (out : List Bool) (i : Fin C.Tc) (hi : i.val < 10) (t : ℕ) (i' : Fin t) (h : i'.val = i.val) :
    C.cellBank r k R L j out i = keyEntry a r k j t i' := by
  unfold CellParts.cellBank keyEntry
  by_cases h9 : i.val = 9
  · rw [if_neg (by omega), if_pos h9, if_pos (by omega)]
  · rw [if_pos (by omega), if_neg (by omega)]
    exact metaEntry_val r k _ _ _ _ h.symm

theorem cellBank_hi {K : KitShape a} (C : CellParts a K) (r : Request) (k : rcKey a r) (R L j : ℕ)
    (out : List Bool) (i : Fin C.Tc) (hi : 12 ≤ i.val) :
    C.cellBank r k R L j out i = List.replicate R false := by
  unfold CellParts.cellBank
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem cell_mid_hin {K : KitShape a} (C : CellParts a K) (r : Request) (k : rcKey a r) (R L j : ℕ)
    (out : List Bool) (mb : ℕ) (hmbR : mb ≤ R) (i : Fin (C.mid.Tm + 1)) :
    C.cellHeads out (C.σM i) = Fin.addCases (motive := fun _ => ℕ) (fun _ : Fin C.mid.Tm => 0) (fun _ : Fin 1 => 0) i ∧
    C.cellBank r k R L j out (C.σM i) = ZeroPadding.pad (if i.val < 10 then 0 else R)
      (Fin.addCases (motive := fun _ => List Bool) (keyEntry a r k j C.mid.Tm)
        (fun _ : Fin 1 => List.replicate mb false) i) := by
  have hTm := C.mid.Tm_ge
  refine ⟨by rw [cellHeads_σM, addCases_zero], ?_⟩
  rw [addCases_val]
  by_cases h10 : i.val < 10
  · rw [dif_pos (by omega), if_pos h10, ZeroPadding.pad_zero]
    exact cellBank_lo C r k R L j out _ (by rw [CellParts.σM_val, if_pos h10]; exact h10) _ _
      (by rw [CellParts.σM_val, if_pos h10])
  · rw [if_neg h10, cellBank_hi C r k R L j out _ (by rw [CellParts.σM_val, if_neg h10]; omega)]
    by_cases hlt : i.val < C.mid.Tm
    · rw [dif_pos hlt]
      have he : keyEntry a r k j C.mid.Tm ⟨i.val, hlt⟩ = [] := by
        simp only [keyEntry, PacketsCombine.metaEntry]
        rw [if_neg (show ¬ (i.val = 9) by omega), if_neg (show ¬ (i.val = 0) by omega),
          dif_neg (show ¬ (1 ≤ i.val ∧ i.val ≤ 8) by omega)]
      rw [he, Dock.pad_nil_eq]
    · rw [dif_neg hlt, Dock.pad_zeros _ _ hmbR, Dock.pad_nil_eq]

/-- Stage 1 of the cell: the masked middle, docked. -/
theorem cell_mid {K : KitShape a} (C : CellParts a K) (hA : ConeBounds.RouteA a K) (r : Request) (k : rcKey a r)
    (hk : k ∈ rcKeys a r) (j : ℕ) (hj : j < maskCount a r k) (out : List Bool) (R L mb : ℕ)
    (hmb : C.mid.midCost r k j ≤ mb) (hmbR : mb ≤ R) :
    ∃ (H1 : Fin C.Tc → ℕ) (A1 : Fin C.Tc → List Bool),
      Step (RecoveryFocus.machine C.σM (MaskedReset.machine C.mid.midMachine (fun _ => true))) (2 * mb + 2)
        (C.cellHeads out) (C.cellBank r k R L j out) H1 A1 ∧
      (∀ i : Fin C.Tc, i.val < 10 → A1 i = C.cellBank r k R L j out i ∧ H1 i = 0) ∧
      A1 ⟨716, by have := C.Tc_ge; omega⟩ = ZeroPadding.pad R (vecOf a K r k j) ∧
      H1 ⟨716, by have := C.Tc_ge; omega⟩ = 0 ∧
      (∀ i : Fin C.Tc, (i.val = 10 ∨ i.val = 11 ∨ C.mid.Tm + 3 ≤ i.val) → A1 i = C.cellBank r k R L j out i ∧
        H1 i = C.cellHeads out i) := by
  have hTm := C.mid.Tm_ge
  refine (mid_run C.mid hA r k hk j hj).elim fun Hm h1 => h1.elim fun Am h2 => ?_
  have sm := h2.1
  have hkm := h2.2.1
  have hvm := h2.2.2
  have smk := (sm.enlarge hmb).mask (fun _ => true) (fun _ _ => rfl) (le_refl mb)
  refine (Dock.lift smk C.σM C.σM_injective (fun i => if i.val < 10 then 0 else R) (C.cellHeads out)
    (C.cellBank r k R L j out) (cell_mid_hin C r k R L j out mb hmbR)).elim fun H1 h3 => h3.elim fun A1 h4 => ?_
  have st := h4.1
  have hs := h4.2.1
  have ho := h4.2.2
  refine ⟨H1, A1, st, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have e : C.σM ⟨i.val, by omega⟩ = i := Fin.ext (by rw [CellParts.σM_val, if_pos hi])
    rw [← e, (hs _).1, (hs _).2, addCases_val, addCases_val]
    rw [dif_pos (show i.val < C.mid.Tm by omega), dif_pos (show i.val < C.mid.Tm by omega)]
    rw [if_pos (show i.val < 10 from hi), ZeroPadding.pad_zero, (hkm ⟨i.val, by omega⟩ hi).1]
    refine ⟨?_, rfl⟩
    exact (cellBank_lo C r k R L j out _ (by rw [CellParts.σM_val, if_pos hi]; exact hi) _ _
      (by rw [CellParts.σM_val, if_pos hi])).symm
  · have e : C.σM ⟨714, by omega⟩ = ⟨716, by have := C.Tc_ge; omega⟩ := Fin.ext (by rw [CellParts.σM_val]; rfl)
    rw [← e, (hs _).2, addCases_val, dif_pos (show (714 : ℕ) < C.mid.Tm by omega)]
    rw [if_neg (show ¬ ((714 : ℕ) < 10) by omega)]
    rw [show (⟨714, by omega⟩ : Fin C.mid.Tm) = C.mid.vecTape from rfl, hvm]
    rfl
  · have e : C.σM ⟨714, by omega⟩ = ⟨716, by have := C.Tc_ge; omega⟩ := Fin.ext (by rw [CellParts.σM_val]; rfl)
    rw [← e, (hs _).1, addCases_val, dif_pos (show (714 : ℕ) < C.mid.Tm by omega)]
    rfl
  · intro i hi
    have hn : ∀ l, C.σM l ≠ i := by
      intro l hl
      have hv := congrArg Fin.val hl
      rw [CellParts.σM_val] at hv
      have := l.isLt
      split_ifs at hv <;> omega
    exact ⟨(ho i hn).2, (ho i hn).1⟩

end
end NearCubicWires.PacketsConstruction.Residual

import Proof.Packets.PacketsResidualHoles

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.Residual
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
noncomputable section

variable {a : DecompositionAlgorithm}

def donorEntry (a : DecompositionAlgorithm) (r : Request) (k : rcKey a r) (Q t : ℕ) (i : Fin t) : List Bool :=
  if i.val < 9 then PacketsCombine.metaEntry a r (some k) t i else List.replicate Q false

structure CoordDonor (a : DecompositionAlgorithm) (K : KitShape a) where
  extra : ℕ
  states : ℕ
  machine : Machine (11 + extra) states
  cost : Request → ℕ
  costC : ℕ
  costD : ℕ
  cost_le : ∀ r, cost r ≤ costC * (r.smallSize a) ^ costD
  padW : Request → ℕ
  padW_pb : PB a padW
  run : ∀ r (k : rcKey a r), k ∈ rcKeys a r →
    ∃ (H : Fin (11 + extra) → ℕ) (A : Fin (11 + extra) → List Bool),
      Step machine (cost r) (fun _ => 0) (donorEntry a r k (padW r) (11 + extra)) H A ∧
      (∀ i : Fin (11 + extra), i.val < 9 → A i = PacketsCombine.metaEntry a r (some k) (11 + extra) i ∧ H i = 0) ∧
      A ⟨9, by omega⟩ = ZeroPadding.pad (padW r) (coordWordK K r k) ∧ H ⟨9, by omega⟩ = 0 ∧
      A ⟨10, by omega⟩ = ZeroPadding.pad (padW r) [modeBit r] ∧ H ⟨10, by omega⟩ = 0

theorem bank_digit {X : WriterShape a} (r : Request) (k : rcKey a r) (i : Fin (10 + X.w)) (h2 : 2 ≤ i.val)
    (h10 : i.val < 10) :
    X.layout.bank r (some k) [] i =
      RepairOrdinary.frame (binary (fieldWidth a r) (keyDigits a r (some k) ⟨i.val - 2, by omega⟩)) := by
  have hne := X.ne_output i (by omega)
  have hs : X.layout.scratch i = false := by simp [WriterShape.layout, digitLayout]; omega
  have hc : X.layout.cursorPort i = true := by simp [WriterShape.layout, digitLayout]; omega
  unfold Layout.bank
  simp only [hne, hs, hc, if_false, if_true, Bool.false_eq_true]
  simp [WriterShape.layout, digitLayout, h2, h10]
  rfl

/-! ## The dock -/

section Dock
variable {X : WriterShape a} (Y : RowPolyShape X) (e : ℕ) (hu : e ≤ Y.u1)

def coordSlotVal (j : ℕ) : ℕ :=
  if j ≤ 8 then (if j = 0 then 0 else j + 1) else if j = 9 then 19 else if j = 10 then 20 else 21 + (j - 11)

def coordSlot (j : Fin (11 + e)) : Fin (10 + X.w) :=
  ⟨coordSlotVal j.val, by
    have h1 := Y.hw1
    have h2 := j.isLt
    unfold coordSlotVal WriterShape.w
    split_ifs <;> omega⟩

theorem coordSlot_val (j : Fin (11 + e)) : (coordSlot Y e hu j).val = coordSlotVal j.val := rfl

theorem coordSlot_injective : Function.Injective (coordSlot Y e hu) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [coordSlot_val, coordSlot_val] at hv
  unfold coordSlotVal at hv
  apply Fin.ext
  split_ifs at hv <;> omega

end Dock

def CoordDonor.stage {K : KitShape a} (d : CoordDonor a K) {X : WriterShape a} (Y : RowPolyShape X)
    (hu : d.extra ≤ Y.u1) (hn : ∀ r, d.padW r ≤ X.R r) : CoordStageK Y K where
  states := _
  machine := RecoveryFocus.machine (coordSlot Y d.extra hu) d.machine
  cost := d.cost
  coefficient := d.costC
  degree := d.costD
  cost_le := d.cost_le
  run := fun r k hk H A hkept hblank => by
    obtain ⟨H1, A1, hs, hkeep, h9A, h9H, h10A, h10H⟩ := d.run r k hk
    have hi := coordSlot_injective Y d.extra hu
    have hw1 := Y.hw1
    obtain ⟨H', A', st, hslot, hother⟩ := Dock.lift hs (coordSlot Y d.extra hu) hi
      (fun j => if j.val ≤ 8 then 0 else X.R r) H A (by
        intro j
        by_cases h8 : j.val ≤ 8
        · have hv : (coordSlot Y d.extra hu j).val = if j.val = 0 then 0 else j.val + 1 := by
            rw [coordSlot_val]; unfold coordSlotVal; simp [h8]
          have hk' := hkept (coordSlot Y d.extra hu j) (by rw [hv]; split_ifs <;> omega)
            (by rw [hv]; split_ifs <;> omega)
          refine ⟨hk'.2, ?_⟩
          rw [hk'.1, if_pos h8, ZeroPadding.pad_zero]
          by_cases h0 : j.val = 0
          · have he : coordSlot Y d.extra hu j = X.port 0 (by omega) := Fin.ext (by rw [hv, if_pos h0]; rfl)
            rw [he, X.bank_zero]
            simp [donorEntry, PacketsCombine.metaEntry, h0]
          · rw [bank_digit (X := X) r k _ (by rw [hv, if_neg h0]; omega) (by rw [hv, if_neg h0]; omega)]
            simp only [donorEntry, if_pos (show j.val < 9 by omega), PacketsCombine.metaEntry,
              PacketsCombine.keyWord, if_neg h0, dif_pos (show 1 ≤ j.val ∧ j.val ≤ 8 from ⟨by omega, h8⟩)]
            congr 3
            apply Fin.ext
            simp only [hv, if_neg h0]
            omega
        · have hv : 19 ≤ (coordSlot Y d.extra hu j).val := by
            rw [coordSlot_val]; unfold coordSlotVal; split_ifs <;> omega
          have hb := hblank (coordSlot Y d.extra hu j) (by
            unfold RowPolyShape.inQ1
            rw [coordSlot_val]
            unfold coordSlotVal
            have := j.isLt
            split_ifs <;> omega)
          refine ⟨hb.2, ?_⟩
          rw [hb.1, if_neg h8]
          simp only [donorEntry, if_neg (show ¬ j.val < 9 by omega)]
          rw [Dock.pad_zeros _ _ (hn r), Dock.pad_nil_eq])
    have s9 : coordSlot Y d.extra hu ⟨9, by omega⟩ = Y.tape 19 (by omega) := Fin.ext rfl
    have s10 : coordSlot Y d.extra hu ⟨10, by omega⟩ = Y.tape 20 (by omega) := Fin.ext rfl
    refine ⟨H', A', st, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← s9, (hslot ⟨9, by omega⟩).2, h9A]
      simp only [show ¬ ((9 : ℕ) ≤ 8) by omega, if_false]
      exact Dock.pad_monotone _ _ _ (hn r)
    · rw [← s9, (hslot ⟨9, by omega⟩).1, h9H]
    · rw [← s10, (hslot ⟨10, by omega⟩).2, h10A]
      simp only [show ¬ ((10 : ℕ) ≤ 8) by omega, if_false]
      exact Dock.pad_monotone _ _ _ (hn r)
    · rw [← s10, (hslot ⟨10, by omega⟩).1, h10H]
    · intro i hq h19 h20
      by_cases hsl : ∃ j, coordSlot Y d.extra hu j = i
      · obtain ⟨j, rfl⟩ := hsl
        have hjv := coordSlot_val Y d.extra hu j
        have h8 : j.val ≤ 8 := by
          by_contra h8
          unfold coordSlotVal at hjv
          apply hq
          unfold RowPolyShape.inQ1
          have := j.isLt
          split_ifs at hjv <;> omega
        have hv : (coordSlot Y d.extra hu j).val = if j.val = 0 then 0 else j.val + 1 := by
          rw [hjv]; unfold coordSlotVal; simp [h8]
        have hk' := hkept (coordSlot Y d.extra hu j) (by rw [hv]; split_ifs <;> omega)
          (by rw [hv]; split_ifs <;> omega)
        have hkj := hkeep j (by omega)
        refine ⟨?_, ?_⟩
        · rw [(hslot j).2, if_pos h8, ZeroPadding.pad_zero, hkj.1]
          -- the entry word of slot `j` is exactly the ambient word (entry computation above)
          have hent : A (coordSlot Y d.extra hu j) = PacketsCombine.metaEntry a r (some k) (11 + d.extra) j := by
            rw [hk'.1]
            by_cases h0 : j.val = 0
            · have he : coordSlot Y d.extra hu j = X.port 0 (by omega) := Fin.ext (by rw [hv, if_pos h0]; rfl)
              rw [he, X.bank_zero]
              simp [PacketsCombine.metaEntry, h0]
            · rw [bank_digit (X := X) r k _ (by rw [hv, if_neg h0]; omega) (by rw [hv, if_neg h0]; omega)]
              simp only [PacketsCombine.metaEntry, PacketsCombine.keyWord, if_neg h0,
              dif_pos (show 1 ≤ j.val ∧ j.val ≤ 8 from ⟨by omega, h8⟩)]
              congr 3
              apply Fin.ext
              simp only [hv, if_neg h0]
              omega
          exact hent.symm
        · rw [(hslot j).1, hkj.2, hk'.2]
      · simp only [not_exists] at hsl
        exact ⟨(hother i hsl).2, (hother i hsl).1⟩

def CoordDonor.fam {K : KitShape a} (d : CoordDonor a K) : CoordFam a K where
  u := d.extra
  need := d.padW
  need_pb := d.padW_pb
  costC := d.costC
  costD := d.costD
  stage := fun Y hu hn => d.stage Y hu hn
  cost_le := fun _ _ _ r => d.cost_le r

end
end NearCubicWires.PacketsConstruction.Residual

import Proof.Packets.PacketsCoordCellRun

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

theorem cell_app_hin {K : KitShape a} (C : CellParts a K) (R : ℕ) (v out : List Bool)
    (H1 : Fin C.Tc → ℕ) (A1 : Fin C.Tc → List Bool)
    (h716 : A1 ⟨716, by have := C.Tc_ge; omega⟩ = ZeroPadding.pad R v ∧ H1 ⟨716, by have := C.Tc_ge; omega⟩ = 0)
    (h11 : A1 ⟨11, by have := C.Tc_ge; omega⟩ = out ∧ H1 ⟨11, by have := C.Tc_ge; omega⟩ = out.length)
    (h10 : A1 ⟨10, by have := C.Tc_ge; omega⟩ = List.replicate v.length true ∧ H1 ⟨10, by have := C.Tc_ge; omega⟩ = 0)
    (hpriv : ∀ i : Fin C.Tc, C.mid.Tm + 3 ≤ i.val → A1 i = List.replicate R false ∧ H1 i = 0)
    (l : Fin (3 + C.app.extra)) :
    H1 (C.σA l) = (fun i : Fin (3 + C.app.extra) => if i.val = 1 then out.length else 0) l ∧
    A1 (C.σA l) = ZeroPadding.pad (if l.val < 3 then 0 else R) (appendEntry R v out (3 + C.app.extra) l) := by
  have hTm := C.mid.Tm_ge
  by_cases h0 : l.val = 0
  · have e : C.σA l = ⟨716, by have := C.Tc_ge; omega⟩ := Fin.ext (by rw [CellParts.σA_val, if_pos h0])
    rw [e, h716.1, h716.2]
    simp [appendEntry, h0]
  · by_cases h1 : l.val = 1
    · have e : C.σA l = ⟨11, by have := C.Tc_ge; omega⟩ := Fin.ext (by rw [CellParts.σA_val, if_neg h0, if_pos h1])
      rw [e, h11.1, h11.2]
      simp [appendEntry, h1]
    · by_cases h2 : l.val = 2
      · have e : C.σA l = ⟨10, by have := C.Tc_ge; omega⟩ :=
          Fin.ext (by rw [CellParts.σA_val, if_neg h0, if_neg h1, if_pos h2])
        rw [e, h10.1, h10.2]
        simp [appendEntry, h2]
      · have hv : (C.σA l).val = C.mid.Tm + 3 + (l.val - 3) := by
          rw [CellParts.σA_val, if_neg h0, if_neg h1, if_neg h2]
        have hp := hpriv (C.σA l) (by rw [hv]; omega)
        rw [hp.1, hp.2]
        simp only [appendEntry, h0, h1, h2, if_false, show ¬ (l.val < 3) by omega, Dock.pad_nil_eq]
        simp

/-- Stage 2 of the cell: the append, docked. -/
theorem cell_app {K : KitShape a} (C : CellParts a K) (R : ℕ) (v out : List Bool) (hvR : v.length ≤ R)
    (H1 : Fin C.Tc → ℕ) (A1 : Fin C.Tc → List Bool)
    (h716 : A1 ⟨716, by have := C.Tc_ge; omega⟩ = ZeroPadding.pad R v ∧ H1 ⟨716, by have := C.Tc_ge; omega⟩ = 0)
    (h11 : A1 ⟨11, by have := C.Tc_ge; omega⟩ = out ∧ H1 ⟨11, by have := C.Tc_ge; omega⟩ = out.length)
    (h10 : A1 ⟨10, by have := C.Tc_ge; omega⟩ = List.replicate v.length true ∧ H1 ⟨10, by have := C.Tc_ge; omega⟩ = 0)
    (hpriv : ∀ i : Fin C.Tc, C.mid.Tm + 3 ≤ i.val → A1 i = List.replicate R false ∧ H1 i = 0) :
    ∃ (H2 : Fin C.Tc → ℕ) (A2 : Fin C.Tc → List Bool),
      Step (RecoveryFocus.machine C.σA C.app.machine) (C.app.cost v.length) H1 A1 H2 A2 ∧
      A2 ⟨11, by have := C.Tc_ge; omega⟩ = out ++ v ∧ H2 ⟨11, by have := C.Tc_ge; omega⟩ = (out ++ v).length ∧
      A2 ⟨10, by have := C.Tc_ge; omega⟩ = List.replicate v.length true ∧ H2 ⟨10, by have := C.Tc_ge; omega⟩ = 0 ∧
      (∀ i : Fin C.Tc, i.val < 10 → A2 i = A1 i ∧ H2 i = H1 i) := by
  have hTm := C.mid.Tm_ge
  refine (C.app.run R v out hvR).elim fun Ha h1 => h1.elim fun Aa h2 => ?_
  have sa := h2.1
  refine (Dock.lift sa C.σA C.σA_injective (fun l => if l.val < 3 then 0 else R) H1 A1
    (cell_app_hin C R v out H1 A1 h716 h11 h10 hpriv)).elim fun H2 h3 => h3.elim fun A2 h4 => ?_
  have st := h4.1
  have hs := h4.2.1
  have ho := h4.2.2
  have e1 : C.σA ⟨1, by omega⟩ = ⟨11, by have := C.Tc_ge; omega⟩ := Fin.ext rfl
  have e2 : C.σA ⟨2, by omega⟩ = ⟨10, by have := C.Tc_ge; omega⟩ := Fin.ext rfl
  refine ⟨H2, A2, st, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← e1, (hs _).2, h2.2.1]; simp
  · rw [← e1, (hs _).1, h2.2.2.1]
  · rw [← e2, (hs _).2, h2.2.2.2.1]; simp
  · rw [← e2, (hs _).1, h2.2.2.2.2]
  · intro i hi
    have hn : ∀ l, C.σA l ≠ i := by
      intro l hl
      have hv := congrArg Fin.val hl
      rw [CellParts.σA_val] at hv
      split_ifs at hv <;> omega
    exact ⟨(ho i hn).2, (ho i hn).1⟩

/-- **The cell stage** (the `stage` field of `Cells.ofScrub`). -/
theorem cell_stage {K : KitShape a} (C : CellParts a K) (hA : ConeBounds.RouteA a K) (r : Request) (k : rcKey a r)
    (hk : k ∈ rcKeys a r) (j : ℕ) (hj : j < maskCount a r k) (out : List Bool) (R L mb : ℕ)
    (hmb : C.mid.midCost r k j ≤ mb) (hmbR : mb ≤ R) (hlen : (vecOf a K r k j).length = L) (hLR : L ≤ R) :
    ∃ (H' : Fin C.Tc → ℕ) (A' : Fin C.Tc → List Bool),
      Step C.cellMachine (CellParts.cellCost mb (C.app.cost L) (maskCount a r k))
        (C.cellHeads out) (C.cellBank r k R L j out) H' A' ∧
      (∀ i, C.cellS i = false → A' i = C.cellBank r k R L (j + 1) (out ++ vecOf a K r k j) i) ∧
      (∀ i, C.cellReset i = false → H' i = C.cellHeads (out ++ vecOf a K r k j) i) := by
  have hTm := C.mid.Tm_ge
  have hTc := C.Tc_ge
  refine (cell_mid C hA r k hk j hj out R L mb hmb hmbR).elim fun H1 h1 => h1.elim fun A1 h2 => ?_
  have s1 := h2.1
  have hlo := h2.2.1
  have h716A := h2.2.2.1
  have h716H := h2.2.2.2.1
  have hrest := h2.2.2.2.2
  have h11 := hrest ⟨11, by omega⟩ (Or.inr (Or.inl rfl))
  have h10 := hrest ⟨10, by omega⟩ (Or.inl rfl)
  refine (cell_app C R (vecOf a K r k j) out (by omega) H1 A1 ⟨h716A, h716H⟩
    ⟨by rw [h11.1]; rfl, by rw [h11.2]; rfl⟩
    ⟨by rw [h10.1, hlen]; rfl, by rw [h10.2]; rfl⟩
    (fun i hi => ⟨by rw [(hrest i (Or.inr (Or.inr hi))).1, cellBank_hi C r k R L j out i (by omega)],
      by rw [(hrest i (Or.inr (Or.inr hi))).2]; unfold CellParts.cellHeads; rw [if_neg (by omega)]⟩)).elim
    fun H2 h3 => h3.elim fun A2 h4 => ?_
  have s2 := h4.1
  have h11A := h4.2.1
  have h11H := h4.2.2.1
  have h10A := h4.2.2.2.1
  have h10H := h4.2.2.2.2.1
  have hlo2 := h4.2.2.2.2.2
  have h9 : H2 ⟨9, by omega⟩ = 0 ∧ A2 ⟨9, by omega⟩ = List.replicate j true := by
    have k9 := hlo2 ⟨9, by omega⟩ (by show 9 < 10; omega)
    have l9 := hlo ⟨9, by omega⟩ (by show 9 < 10; omega)
    refine ⟨by rw [k9.2, l9.2], ?_⟩
    rw [k9.1, l9.1]
    simp [CellParts.cellBank]
  refine (liftExact (IncrM.run j) C.σI C.σI_injective H2 A2 (fun _ => h9)).elim fun H3 h5 => h5.elim
    fun A3 h6 => ?_
  have s3 := h6.1
  have hs3 := h6.2.1
  have ho3 := h6.2.2
  have hn9 : ∀ i : Fin C.Tc, i.val ≠ 9 → ∀ l, C.σI l ≠ i := by
    intro i hi l hl
    have := congrArg Fin.val hl
    exact hi (by rw [← this]; rfl)
  refine ⟨H3, A3, ((s1.seq s2).seq s3).enlarge (by unfold CellParts.cellCost; rw [hlen]; omega), ?_, ?_⟩
  · intro i hi
    have hi12 : i.val < 12 := by simpa [CellParts.cellS] using hi
    by_cases e9 : i.val = 9
    · have e : i = C.σI 0 := Fin.ext e9
      rw [e, (hs3 0).2]
      simp [CellParts.cellBank, CellParts.σI]
    · rw [(ho3 i (hn9 i e9)).2]
      by_cases hlt : i.val < 10
      · rw [(hlo2 i hlt).1, (hlo i hlt).1]
        unfold CellParts.cellBank
        rw [if_pos (by omega), if_pos (by omega)]
      · by_cases e10 : i.val = 10
        · have e : i = ⟨10, by omega⟩ := Fin.ext e10
          rw [e, h10A, hlen]
          simp [CellParts.cellBank]
        · have e : i = ⟨11, by omega⟩ := Fin.ext (show i.val = 11 by omega)
          rw [e, h11A]
          simp [CellParts.cellBank]
  · intro i hi
    have e11 : i.val = 11 := by simpa [CellParts.cellReset] using hi
    have e : i = ⟨11, by omega⟩ := Fin.ext e11
    have hn : ∀ l, C.σI l ≠ ⟨11, by omega⟩ := hn9 ⟨11, by omega⟩ (by simp)
    rw [e, (ho3 _ hn).1, h11H]
    simp [CellParts.cellHeads]

end
end NearCubicWires.PacketsConstruction.Residual

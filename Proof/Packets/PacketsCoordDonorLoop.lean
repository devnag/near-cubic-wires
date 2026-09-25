import Proof.Packets.PacketsCoordPre

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.Residual.Donor
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.BlockPlatform
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
noncomputable section

variable {a : DecompositionAlgorithm}

/-! ## The masked loop's banks, by value -/

section Vals
variable {K : KitShape a} (C : CellParts a K)

theorem bankM_val (r : Request) (k : rcKey a r) (R L Llog cap M j : ℕ) (out : List Bool)
    (l : Fin (C.Tc + 1 + 1 + 1 + 1)) :
    Fin.addCases (motive := fun _ => List Bool)
      (Fin.addCases (motive := fun _ => List Bool) (Scrub.bank (C.cellBank r k R L j out) R Llog)
        (fun _ : Fin 1 => CompareMachine.word M)) (fun _ : Fin 1 => List.replicate cap false) l =
      if h : l.val < C.Tc then C.cellBank r k R L j out ⟨l.val, h⟩
      else if l.val = C.Tc then List.replicate Llog false
      else if l.val = C.Tc + 1 then List.replicate R true
      else if l.val = C.Tc + 2 then CompareMachine.word M
      else List.replicate cap false := by
  simp only [Scrub.bank, addCases_val]
  split_ifs <;> first | rfl | omega

theorem headsM_val (out : List Bool) (l : Fin (C.Tc + 1 + 1 + 1 + 1)) :
    Fin.addCases (motive := fun _ => ℕ)
      (Fin.addCases (motive := fun _ => ℕ) (Scrub.heads (C.cellHeads out)) (fun _ : Fin 1 => 1))
      (fun _ : Fin 1 => 0) l =
      if l.val = 11 then out.length else if l.val = C.Tc + 2 then 1 else 0 := by
  have := C.Tc_ge
  simp only [Scrub.heads, addCases_val, CellParts.cellHeads]
  split_ifs <;> first | rfl | omega

/-- The output tape of the loop layout (the masked reset's selection). -/
def selOut (i : Fin (C.Tc + 1 + 1 + 1)) : Bool := decide (i.val = 11)

theorem headsX_val (out : List Bool) (l : Fin (C.Tc + 1 + 1 + 1 + 1)) :
    Fin.addCases (motive := fun _ => ℕ)
      (fun i => if selOut C i = true then 0 else
        Fin.addCases (motive := fun _ => ℕ) (Scrub.heads (C.cellHeads out)) (fun _ : Fin 1 => 1) i)
      (fun _ : Fin 1 => 0) l =
      if l.val = C.Tc + 2 then 1 else 0 := by
  have := C.Tc_ge
  simp only [selOut, Scrub.heads, addCases_val, CellParts.cellHeads, decide_eq_true_eq]
  split_ifs <;> first | rfl | omega

end Vals

/-! ## The slot map -/

def σLv (Tc v : ℕ) : ℕ :=
  if v < 9 then v else if v = 9 then 11 else if v = 10 then 12 else if v = 11 then 9 else if v < Tc then v + 5
  else if v = Tc then 13 else if v = Tc + 1 then 14 else if v = Tc + 2 then 15 else 16

/-- Its inverse on the image. -/
def σLinv (Tc w : ℕ) : ℕ :=
  if w < 9 then w else if w = 9 then 11 else if w = 11 then 9 else if w = 12 then 10 else if w = 13 then Tc
  else if w = 14 then Tc + 1 else if w = 15 then Tc + 2 else if w = 16 then Tc + 3 else w - 5

theorem σLinv_σLv (Tc v : ℕ) (_hT : 12 ≤ Tc) (hv : v < Tc + 1 + 1 + 1 + 1) : σLinv Tc (σLv Tc v) = v := by
  unfold σLv
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · unfold σLinv; rw [if_pos h1]
  · subst h2; rfl
  · subst h3; rfl
  · subst h4; rfl
  · unfold σLinv
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    omega
  · unfold σLinv; simp only [show ¬ ((13 : ℕ) < 9) by omega, if_false, show (13 : ℕ) ≠ 9 by omega,
      show (13 : ℕ) ≠ 11 by omega, show (13 : ℕ) ≠ 12 by omega, if_true]; omega
  · unfold σLinv; simp only [show ¬ ((14 : ℕ) < 9) by omega, if_false, show (14 : ℕ) ≠ 9 by omega,
      show (14 : ℕ) ≠ 11 by omega, show (14 : ℕ) ≠ 12 by omega, show (14 : ℕ) ≠ 13 by omega, if_true]; omega
  · unfold σLinv; simp only [show ¬ ((15 : ℕ) < 9) by omega, if_false, show (15 : ℕ) ≠ 9 by omega,
      show (15 : ℕ) ≠ 11 by omega, show (15 : ℕ) ≠ 12 by omega, show (15 : ℕ) ≠ 13 by omega,
      show (15 : ℕ) ≠ 14 by omega, if_true]; omega
  · unfold σLinv; simp only [show ¬ ((16 : ℕ) < 9) by omega, if_false, show (16 : ℕ) ≠ 9 by omega,
      show (16 : ℕ) ≠ 11 by omega, show (16 : ℕ) ≠ 12 by omega, show (16 : ℕ) ≠ 13 by omega,
      show (16 : ℕ) ≠ 14 by omega, show (16 : ℕ) ≠ 15 by omega, if_true]; omega

namespace Parts
variable {K : KitShape a} (D : Parts a K)

def σL (l : Fin (D.cell.Tc + 1 + 1 + 1 + 1)) : Fin D.T :=
  ⟨σLv D.cell.Tc l.val, by
    have h1 := D.sizes; have h2 := D.cell.Tc_ge; have h3 := l.isLt
    unfold σLv S at *; split_ifs <;> omega⟩

theorem σL_val (l : Fin (D.cell.Tc + 1 + 1 + 1 + 1)) : (D.σL l).val = σLv D.cell.Tc l.val := rfl

theorem σL_injective : Function.Injective D.σL := by
  intro x y h
  have hv : σLv D.cell.Tc x.val = σLv D.cell.Tc y.val := congrArg Fin.val h
  have := D.cell.Tc_ge
  have e := congrArg (σLinv D.cell.Tc) hv
  rw [σLinv_σLv _ _ (by omega) x.isLt, σLinv_σLv _ _ (by omega) y.isLt] at e
  exact Fin.ext e

/-- **The main machine**: the masked loop, docked. -/
def mainMachine := RecoveryFocus.machine D.σL
  (MaskedReset.machine (CloseoutRowsDegreeLoop.machine (Scrub.machine D.cell.cellMachine D.cell.cellReset D.cell.cellS))
    (selOut D.cell))

end Parts

/-- **The main phase**: from the pre-phase's state to the coordinate word on tape 9 (head 0). -/
theorem main_run {K : KitShape a} (D : Parts a K) (hA : ConeBounds.RouteA a K) (r : Request) (k : rcKey a r)
    (hk : k ∈ rcKeys a r) (Llog mb cap : ℕ)
    (hmb : ∀ j, j < maskCount a r k → D.cell.mid.midCost r k j ≤ mb) (hmbR : mb ≤ D.Rv r)
    (hlen : ∀ j, j < maskCount a r k → (vecOf a K r k j).length = D.Lv r) (hLR : D.Lv r ≤ D.Rv r)
    (hR : CellParts.cellCost mb (D.cell.app.cost (D.Lv r)) (maskCount a r k) + 1 ≤ D.Rv r) (hL : D.Rv r + 1 ≤ Llog)
    (hcap : maskCount a r k * (2 * CellParts.cellCost mb (D.cell.app.cost (D.Lv r)) (maskCount a r k) + 2 + 1 +
      (2 * D.Rv r + 4) + 3) + 3 ≤ cap)
    (H : Fin D.T → ℕ) (A : Fin D.T → List Bool)
    (hI : DInv a r k D.T D.S (modeBit r) (D.Lv r) (D.Rv r) Llog cap (maskCount a r k) Parts.W4 D.T H A) :
    ∃ (H' : Fin D.T → ℕ) (A' : Fin D.T → List Bool),
      Step D.mainMachine (2 * cap + 2) (Function.update H D.cnt 1) A H' A' ∧
      (∀ i : Fin D.T, i.val < 9 → A' i = PacketsCombine.metaEntry a r (some k) D.T i ∧ H' i = 0) ∧
      A' ⟨9, by have := D.T_ge; omega⟩ = coordWordK K r k ∧ H' ⟨9, by have := D.T_ge; omega⟩ = 0 ∧
      A' ⟨10, by have := D.T_ge; omega⟩ = [modeBit r] ∧ H' ⟨10, by have := D.T_ge; omega⟩ = 0 := by
  have hTc := D.cell.Tc_ge
  have hsz := D.sizes
  have hW := portWord_W4 (modeBit r) (D.Lv r) (D.Rv r) Llog cap (maskCount a r k)
  have sl := loop_run D.cell hA r k hk (D.Rv r) (D.Lv r) Llog mb hmb hmbR hlen hLR hR hL
  have sm := (sl.mask (selOut D.cell) (fun i hi => by
    have hi' : i.val = 11 := by simpa [selOut] using hi
    simp only [Scrub.heads, addCases_val, CellParts.cellHeads]
    split_ifs <;> first | rfl | omega) hcap).enlarge (show _ ≤ 2 * cap + 2 by omega)
  refine (liftExact sm D.σL D.σL_injective (Function.update H D.cnt 1) A (by
    intro l
    rw [bankM_val, headsM_val]
    have hlt := l.isLt
    by_cases h9 : l.val < 9
    · have hv : (D.σL l).val = l.val := by rw [Parts.σL_val]; unfold σLv; rw [if_pos h9]
      have hne : D.σL l ≠ D.cnt := fun e => by have := congrArg Fin.val e; rw [hv] at this; unfold Parts.cnt at this; simp at this; omega
      rw [Function.update_of_ne hne, (hI.key _ (by omega)).1, (hI.key _ (by omega)).2,
        if_neg (show ¬ (l.val = 11) by omega), if_neg (show ¬ (l.val = D.cell.Tc + 2) by omega),
        dif_pos (show l.val < D.cell.Tc by omega)]
      refine ⟨rfl, ?_⟩
      unfold CellParts.cellBank
      rw [if_pos (show (⟨l.val, (by omega : l.val < D.cell.Tc)⟩ : Fin D.cell.Tc).val < 9 from h9)]
      exact Residual.metaEntry_val r k _ _ _ _ hv
    · by_cases hlo : l.val < D.cell.Tc
      · rw [dif_pos hlo, if_neg (show ¬ (l.val = D.cell.Tc + 2) by omega)]
        by_cases h12 : 12 ≤ l.val
        · have hv : (D.σL l).val = l.val + 5 := by
            rw [Parts.σL_val]; unfold σLv
            rw [if_neg h9, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hlo]
          have hne : D.σL l ≠ D.cnt := fun e => by have := congrArg Fin.val e; rw [hv] at this; unfold Parts.cnt at this; simp at this; omega
          have hs := hI.scratch (D.σL l) (by omega) (by rw [hv]; unfold Parts.S; omega)
          rw [Function.update_of_ne hne, hs.1, hs.2, if_neg (show ¬ (l.val = 11) by omega),
            cellBank_hi D.cell r k _ _ _ _ _ (show 12 ≤ (⟨l.val, hlo⟩ : Fin D.cell.Tc).val from h12)]
          exact ⟨rfl, rfl⟩
        · have hp : ∀ i : Fin D.T, i.val = (D.σL l).val → 9 ≤ i.val ∧ i.val < 17 := by
            intro i hi; rw [Parts.σL_val] at hi; unfold σLv at hi
            rw [if_neg h9] at hi; split_ifs at hi <;> omega
          have hq := hI.port (D.σL l) (hp _ rfl).1 (hp _ rfl).2
          have hne : D.σL l ≠ D.cnt := fun e => by
            have hv : σLv D.cell.Tc l.val = 15 := congrArg Fin.val e
            unfold σLv at hv
            rw [if_neg h9] at hv
            split_ifs at hv <;> omega
          rw [Function.update_of_ne hne, hq.1, hq.2]
          unfold CellParts.cellBank
          simp only [show ¬ ((⟨l.val, hlo⟩ : Fin D.cell.Tc).val < 9) from h9]
          have h911 : l.val = 9 ∨ l.val = 10 ∨ l.val = 11 := by omega
          rcases h911 with h | h | h
          · have hv : (D.σL l).val = 11 := by rw [Parts.σL_val]; unfold σLv; rw [if_neg h9, if_pos h]
            rw [hv]
            simp [h, portWord]
          · have hv : (D.σL l).val = 12 := by
              rw [Parts.σL_val]; unfold σLv; rw [if_neg h9, if_neg (by omega), if_pos h]
            rw [hv, hW.2.1]
            simp [h]
          · have hv : (D.σL l).val = 9 := by
              rw [Parts.σL_val]; unfold σLv; rw [if_neg h9, if_neg (by omega), if_neg (by omega), if_pos h]
            rw [hv]
            simp [h, portWord]
      · rw [dif_neg hlo]
        have hq : ∀ v, (D.σL l).val = v → 13 ≤ v ∧ v ≤ 16 := by
          intro v hv; rw [Parts.σL_val] at hv; unfold σLv at hv
          rw [if_neg h9, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg hlo] at hv
          split_ifs at hv <;> omega
        have hp := hI.port (D.σL l) (by have := hq _ rfl; omega) (by have := hq _ rfl; omega)
        have hv : (D.σL l).val = σLv D.cell.Tc l.val := rfl
        unfold σLv at hv
        rw [if_neg h9, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg hlo] at hv
        by_cases hc : l.val = D.cell.Tc + 2
        · have hv' : D.σL l = D.cnt := Fin.ext (by rw [hv, if_neg (by omega), if_neg (by omega), if_pos hc]; rfl)
          rw [hv', Function.update_self, if_neg (show ¬ (l.val = 11) by omega), if_pos hc, ← hv', hp.1]
          refine ⟨rfl, ?_⟩
          rw [hv, if_neg (by omega), if_neg (by omega), if_pos hc, hW.2.2.2, if_neg (by omega), if_neg (by omega),
            if_pos hc]
        · have hne : D.σL l ≠ D.cnt := fun e => by
            have := congrArg Fin.val e; rw [hv] at this; unfold Parts.cnt at this; simp only at this
            split_ifs at this <;> omega
          rw [Function.update_of_ne hne, hp.2, if_neg (show ¬ (l.val = 11) by omega), if_neg hc, hp.1]
          refine ⟨rfl, ?_⟩
          rw [hv]
          by_cases h0 : l.val = D.cell.Tc
          · rw [if_pos h0, if_pos h0]; simp [portWord]
          · by_cases h1 : l.val = D.cell.Tc + 1
            · rw [if_neg h0, if_pos h1, if_neg h0, if_pos h1, hW.2.2.1]
            · rw [if_neg h0, if_neg h1, if_neg hc, if_neg h0, if_neg h1, if_neg hc]; simp [portWord])).elim
    fun H' e => e.elim fun A' f => ?_
  have st := f.1
  have hs := f.2.1
  have ho := f.2.2
  refine ⟨H', A', st, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have e : D.σL ⟨i.val, by omega⟩ = i := Fin.ext (by rw [Parts.σL_val]; unfold σLv; rw [if_pos hi])
    rw [← e, (hs _).1, (hs _).2, bankM_val, headsX_val]
    rw [dif_pos (show i.val < D.cell.Tc by omega), if_neg (show ¬ (i.val = D.cell.Tc + 2) by omega)]
    refine ⟨?_, rfl⟩
    unfold CellParts.cellBank
    rw [if_pos (show (⟨i.val, (by omega : i.val < D.cell.Tc)⟩ : Fin D.cell.Tc).val < 9 from hi)]
    exact Residual.metaEntry_val r k _ _ _ _ (by rw [Parts.σL_val]; unfold σLv; rw [if_pos hi])
  · have e : D.σL ⟨11, by omega⟩ = ⟨9, by have := D.T_ge; omega⟩ := Fin.ext (by rw [Parts.σL_val]; rfl)
    rw [← e, (hs _).2, bankM_val, dif_pos (show (11 : ℕ) < D.cell.Tc by omega)]
    rfl
  · have e : D.σL ⟨11, by omega⟩ = ⟨9, by have := D.T_ge; omega⟩ := Fin.ext (by rw [Parts.σL_val]; rfl)
    rw [← e, (hs _).1, headsX_val, if_neg (show ¬ ((11 : ℕ) = D.cell.Tc + 2) by omega)]
  · have hn : ∀ l, D.σL l ≠ ⟨10, by have := D.T_ge; omega⟩ := by
      intro l hl
      have hv : σLv D.cell.Tc l.val = 10 := congrArg Fin.val hl
      unfold σLv at hv
      have := l.isLt
      split_ifs at hv <;> omega
    rw [(ho _ hn).2, (hI.port ⟨10, by have := D.T_ge; omega⟩ (by simp) (by simp)).1, hW.1]
  · have hn : ∀ l, D.σL l ≠ ⟨10, by have := D.T_ge; omega⟩ := by
      intro l hl
      have hv : σLv D.cell.Tc l.val = 10 := congrArg Fin.val hl
      unfold σLv at hv
      have := l.isLt
      split_ifs at hv <;> omega
    have hne : (⟨10, by have := D.T_ge; omega⟩ : Fin D.T) ≠ D.cnt := fun e => by
      have := congrArg Fin.val e; unfold Parts.cnt at this; simp at this
    rw [(ho _ hn).1, Function.update_of_ne hne, (hI.port ⟨10, by have := D.T_ge; omega⟩ (by simp) (by simp)).2]

end
end NearCubicWires.PacketsConstruction.Residual.Donor

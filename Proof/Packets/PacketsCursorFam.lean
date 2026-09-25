import Proof.Packets.PacketsCursorRun

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.Cursor
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketFamilyParent
open NearCubicWires.PacketsConstruction NearCubicWires.PacketsConstruction.Residual
open NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.PacketsMeta.Keys
open NearCubicWires.PacketsGlue.CursorKit NearCubicWires.PacketsGlue.CursorChain NearCubicWires.BlockPlatform
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

variable {a : DecompositionAlgorithm}

/-! ## The whole stage run -/

section Stage
variable {base : Request → ℕ} (V : KeyVec a 9 (cursorOuts a base)) (cE kE : ℕ)

/-- The stage machine's cost at one request. -/
def stageCost (r : Request) : ℕ :=
  ((((2 * V.cost r + 2 + 1 + PacketsGlue.DriverPhase.cost cE kE (base r + 1)) + 1 + (2 * Ev cE kE base r + 4)) + 1 +
    (chainCost (PacketsConstruction.fieldWidth a r) (chainOf r) + 2)) + 1 + (2 * Ev cE kE base r + 4)) + 1 +
    (2 * Ev cE kE base r + 2)

/-- **The stage run**: `sEntry → sExit`, all heads `0 → 0`. -/
theorem stage_run (r : Request) (k : rcKey a r) (hk : k ∈ rcKeys a r)
    (hE1 : base r + 2 ≤ Ev cE kE base r) (hE2 : 2 * V.cost r + 3 ≤ Ev cE kE base r)
    (hE3 : 2 * PacketsConstruction.fieldWidth a r + 1 ≤ Ev cE kE base r) :
    Step (stageM V cE kE) (stageCost V cE kE r) (fun _ => 0) (sEntry a V.extra kE r k (Ev cE kE base r)) (fun _ => 0)
      (sExit a base V.extra kE r k (Ev cE kE base r)) := by
  obtain ⟨A1, s1, h9, hK, hL, hD, hlen⟩ := run1 V kE r k hk (Ev cE kE base r)
  obtain ⟨A2, s2, hA2⟩ := run2 V cE kE r k A1 hK hL hD
  have s3 := run3 V cE kE r k A1 A2 h9 hK hlen hA2 hE1 hE2
  have s4 := run4 V kE r k hk (Ev cE kE base r) hE3
  have s5 := run5 V kE r k (Ev cE kE base r) (by omega)
  have s6 := run6 V kE r k (Ev cE kE base r)
  exact ((((s1.seq s2).seq s3).seq s4).seq s5).seq s6

end Stage

/-! ## The layout dock -/

section Dock
variable (eV kE w : ℕ) (hw : TS eV kE ≤ 9 + w)

/-- Stage tape `0 ↦ 0` (the input), `t ↦ t + 1` (skipping the output tape 1). -/
def ιw (t : Fin (TS eV kE)) : Fin (10 + w) :=
  ⟨if t.val = 0 then 0 else t.val + 1, by have := t.isLt; split_ifs <;> omega⟩

theorem ιw_val (t : Fin (TS eV kE)) : (ιw eV kE w hw t).val = if t.val = 0 then 0 else t.val + 1 := rfl

theorem ιw_inj : Function.Injective (ιw eV kE w hw) := by
  intro x y h
  have hv := congrArg Fin.val h
  rw [ιw_val, ιw_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem ιw_ne_one (t : Fin (TS eV kE)) : (ιw eV kE w hw t).val ≠ 1 := by
  rw [ιw_val]; split_ifs <;> omega

end Dock

section Layout
variable {w : ℕ} {R : Request → ℕ} {cR dR : ℕ} {hR : ∀ r, R r ≤ cR * (r.smallSize a) ^ dR}

theorem lay_heads (out : List Bool) (i : Fin (digitLayout a w R cR dR hR).tapes) (hi : i.val ≠ 1) :
    (digitLayout a w R cR dR hR).heads out i = 0 := by
  have hne : i ≠ (digitLayout a w R cR dR hR).output := fun h => hi (by rw [h]; rfl)
  unfold Layout.heads
  simp only [hne, if_false]

theorem lay_out (r : Request) (c : Option (rcKey a r)) (out : List Bool) (i : Fin (digitLayout a w R cR dR hR).tapes)
    (hi : i.val = 1) : (digitLayout a w R cR dR hR).bank r c out i = out := by
  have e : i = (digitLayout a w R cR dR hR).output := Fin.ext hi
  unfold Layout.bank
  simp only [e, if_true]

theorem lay_scratch (r : Request) (c : Option (rcKey a r)) (out : List Bool) (i : Fin (digitLayout a w R cR dR hR).tapes)
    (hi : 10 ≤ i.val) : (digitLayout a w R cR dR hR).bank r c out i = List.replicate (R r) false := by
  have hne : i ≠ (digitLayout a w R cR dR hR).output := fun h => by
    have hv : i.val = 1 := by rw [h]; rfl
    omega
  have hs : (digitLayout a w R cR dR hR).scratch i = true := by simp [digitLayout]; omega
  unfold Layout.bank
  simp only [hne, hs, if_false, if_true]
  rfl

theorem lay_zero (r : Request) (c : Option (rcKey a r)) (out : List Bool) (i : Fin (digitLayout a w R cR dR hR).tapes)
    (hi : i.val = 0) : (digitLayout a w R cR dR hR).bank r c out i = frame (Request.input a r) := by
  have hne : i ≠ (digitLayout a w R cR dR hR).output := fun h => by
    have hv : i.val = 1 := by rw [h]; rfl
    omega
  have hs : (digitLayout a w R cR dR hR).scratch i = false := by simp [digitLayout]; omega
  have hc : (digitLayout a w R cR dR hR).cursorPort i = false := by simp [digitLayout]; omega
  unfold Layout.bank
  simp only [hne, hs, hc, if_false, Bool.false_eq_true]
  simp [digitLayout, hi]

theorem lay_port (r : Request) (c : Option (rcKey a r)) (out : List Bool) (i : Fin (digitLayout a w R cR dR hR).tapes)
    (h2 : 2 ≤ i.val) (h10 : i.val < 10) :
    (digitLayout a w R cR dR hR).bank r c out i =
      fb (PacketsConstruction.fieldWidth a r) (keyDigits a r c ⟨i.val - 2, by omega⟩) := by
  have hne : i ≠ (digitLayout a w R cR dR hR).output := fun h => by
    have hv : i.val = 1 := by rw [h]; rfl
    omega
  have hs : (digitLayout a w R cR dR hR).scratch i = false := by simp [digitLayout]; omega
  have hc : (digitLayout a w R cR dR hR).cursorPort i = true := by simp [digitLayout]; omega
  unfold Layout.bank
  simp only [hne, hs, hc, if_false, if_true, Bool.false_eq_true]
  simp [digitLayout, h2, h10]

end Layout

/-- The padding caps: `0` on the input and key ports, `Q` on the scratch. -/
def capS (eV kE Q : ℕ) (t : Fin (TS eV kE)) : ℕ := if t.val < 9 then 0 else Q

/-- **One cursor step at one layout**, from the stage machine's exact run. -/
theorem advance_at {base : Request → ℕ} (V : KeyVec a 9 (cursorOuts a base)) (cE kE : ℕ)
    (hE : ∀ r, base r + 2 ≤ Ev cE kE base r ∧ 2 * V.cost r + 3 ≤ Ev cE kE base r ∧
      2 * PacketsConstruction.fieldWidth a r + 1 ≤ Ev cE kE base r)
    (w : ℕ) (R : Request → ℕ) (cR dR : ℕ) (hR : ∀ r, R r ≤ cR * (r.smallSize a) ^ dR)
    (hw : TS V.extra kE ≤ 9 + w) (hn : ∀ r, Ev cE kE base r + 1 ≤ R r)
    (r : Request) (j : ℕ) (hj : j < (rcKeys a r).length) (out : List Bool) :
    Step (RecoveryFocus.machine (ιw V.extra kE w hw) (stageM V cE kE)) (stageCost V cE kE r)
      ((digitLayout a w R cR dR hR).heads out) ((digitLayout a w R cR dR hR).bank r (rcKeys a r)[j]? out)
      ((digitLayout a w R cR dR hR).heads out) ((digitLayout a w R cR dR hR).bank r (rcKeys a r)[j+1]? out) := by
    have hk : (rcKeys a r)[j] ∈ rcKeys a r := List.getElem_mem hj
    have hj' : (rcKeys a r)[j]? = some (rcKeys a r)[j] := List.getElem?_eq_getElem hj
    have hsucc := PacketsGlue.succ_spec a r j hj
    rw [hj'] at hsucc
    have eIn : (digitLayout a w R cR dR hR).bank r (rcKeys a r)[j]? out =
        (digitLayout a w R cR dR hR).bank r (some (rcKeys a r)[j]) out :=
      congrArg (fun c => (digitLayout a w R cR dR hR).bank r c out) hj'
    obtain ⟨hE1, hE2, hE3⟩ := hE r
    have st := stage_run V cE kE r (rcKeys a r)[j] hk hE1 hE2 hE3
    have hQ := hn r
    obtain ⟨H', A', st', hs, ho⟩ := Dock.lift st (ιw V.extra kE w hw) (ιw_inj _ _ _ _)
      (capS V.extra kE (R r)) ((digitLayout a w R cR dR hR).heads out)
      ((digitLayout a w R cR dR hR).bank r (some (rcKeys a r)[j]) out) (by
        intro t
        refine ⟨lay_heads out _ (ιw_ne_one _ _ _ _ t), ?_⟩
        unfold capS sEntry
        have hv := ιw_val V.extra kE w hw t
        by_cases h0 : t.val = 0
        · rw [if_pos (by omega), if_pos (by omega), ZeroPadding.pad_zero, lay_zero r _ out _ (by rw [hv, if_pos h0])]
          unfold PacketsCombine.metaEntry
          rw [if_pos h0]
        · by_cases h9 : t.val < 9
          · rw [if_pos h9, if_pos h9, ZeroPadding.pad_zero,
              lay_port r _ out _ (by rw [hv, if_neg h0]; omega) (by rw [hv, if_neg h0]; omega)]
            rw [me_field r (some (rcKeys a r)[j]) ⟨t.val - 1, by omega⟩ t (by simp; omega)]
            congr 3
            simp only [hv, if_neg h0]
            omega
          · rw [if_neg h9, if_neg h9, lay_scratch r _ out _ (by rw [hv, if_neg h0]; omega)]
            split_ifs
            · rw [Dock.pad_zeros _ _ (by omega), Dock.pad_nil_eq]
            · rw [Dock.pad_nil_eq])
    refine (st'.congr ?_ ?_).congr_in rfl eIn.symm
    · funext i
      by_cases hi : ∃ t, ιw V.extra kE w hw t = i
      · obtain ⟨t, rfl⟩ := hi
        rw [(hs t).1, lay_heads out _ (ιw_ne_one _ _ _ _ t)]
      · simp only [not_exists] at hi
        exact (ho i hi).1
    · funext i
      by_cases hi : ∃ t, ιw V.extra kE w hw t = i
      · obtain ⟨t, rfl⟩ := hi
        rw [(hs t).2]
        have hv := ιw_val V.extra kE w hw t
        unfold capS sExit s5 s4 s3
        by_cases h0 : t.val = 0
        · rw [lay_zero r _ out _ (by rw [hv, if_pos h0]), if_pos (by omega), if_neg (by unfold iD; omega),
            if_neg (by omega), dif_neg (by omega), if_pos (by omega), ZeroPadding.pad_zero]
          unfold PacketsCombine.metaEntry
          rw [if_pos h0]
        · by_cases h9 : t.val < 9
          · rw [lay_port r _ out _ (by rw [hv, if_neg h0]; omega) (by rw [hv, if_neg h0]; omega),
              if_pos h9, if_neg (by unfold iD; omega), if_neg (by omega), dif_pos (by omega), ZeroPadding.pad_zero,
              hsucc]
            congr 2
            apply Fin.ext
            simp only [hv, if_neg h0]
            omega
          · rw [lay_scratch r _ out _ (by rw [hv, if_neg h0]; omega), if_neg h9]
            by_cases hD : t.val = iD V.extra
            · rw [if_pos hD, Dock.pad_zeros _ _ (by omega), Dock.pad_nil_eq]
            · rw [if_neg hD]
              by_cases hm : 9 ≤ t.val ∧ t.val < 17
              · rw [if_pos hm, Dock.pad_zeros _ _ (by omega), Dock.pad_nil_eq]
              · rw [if_neg hm, dif_neg (by omega), if_neg h9, if_neg (by omega)]
                by_cases hL : t.val = iL V.extra
                · rw [if_pos hL, Dock.pad_zeros _ _ (by omega), Dock.pad_nil_eq]
                · rw [if_neg hL, if_neg hD, Dock.pad_zeros _ _ (by omega), Dock.pad_nil_eq]
      · simp only [not_exists] at hi
        rw [(ho i hi).2]
        by_cases h1 : i.val = 1
        · rw [lay_out r _ out i h1, lay_out r _ out i h1]
        · have h10 : 10 ≤ i.val := by
            by_contra hc
            by_cases hz : i.val = 0
            · exact hi ⟨0, by unfold TS; omega⟩ (Fin.ext (by rw [ιw_val]; simp [hz]))
            · exact hi ⟨i.val - 1, by unfold TS; omega⟩ (Fin.ext (by
                rw [ιw_val]
                show (if i.val - 1 = 0 then 0 else i.val - 1 + 1) = i.val
                split_ifs <;> omega))
          rw [lay_scratch r _ out i h10, lay_scratch r _ out i h10]

/-- **The cursor at one layout.** -/
def cursorAt {base : Request → ℕ} (V : KeyVec a 9 (cursorOuts a base)) (cE kE : ℕ)
    (cC dC : ℕ) (hC : ∀ r, stageCost V cE kE r ≤ cC * (r.smallSize a) ^ dC)
    (hE : ∀ r, base r + 2 ≤ Ev cE kE base r ∧ 2 * V.cost r + 3 ≤ Ev cE kE base r ∧
      2 * PacketsConstruction.fieldWidth a r + 1 ≤ Ev cE kE base r)
    (w : ℕ) (R : Request → ℕ) (cR dR : ℕ) (hR : ∀ r, R r ≤ cR * (r.smallSize a) ^ dR)
    (hw : TS V.extra kE ≤ 9 + w) (hn : ∀ r, Ev cE kE base r + 1 ≤ R r) :
    CursorAdvance (digitLayout a w R cR dR hR) where
  states := _
  machine := RecoveryFocus.machine (ιw V.extra kE w hw) (stageM V cE kE)
  cost := stageCost V cE kE
  coefficient := cC
  degree := dC
  cost_le := hC
  advance := fun r j hj out => advance_at V cE kE hE w R cR dR hR hw hn r j hj out

/-! ## The family: constants, bounds, `CursorFam a` -/

theorem chainCost_le (W : ℕ) : ∀ fs : List (Fin 8), chainCost W fs ≤ (fs.length + 1) * (8 * W + 10)
  | [] => by simp only [chainCost, List.length_nil]; omega
  | f :: fs => by
    have ih := chainCost_le W fs
    simp only [chainCost, List.length_cons]
    rw [show (fs.length + 1 + 1) * (8 * W + 10) = (fs.length + 1) * (8 * W + 10) + (8 * W + 10) by ring]
    omega

theorem chainOf_length (r : Request) : (chainOf r).length ≤ 7 := by
  unfold chainOf; split_ifs <;> simp [thrChain, symChain]

theorem width_pb : PB a (fun r => PacketsConstruction.fieldWidth a r) := by
  obtain ⟨c, d, h⟩ := digit_kb a
  exact ⟨c, d, fun r => (width_le_bound a r).trans (h r)⟩

theorem Ev_pb {base : Request → ℕ} (hbp : PB a base) (cE kE : ℕ) : PB a (Ev cE kE base) :=
  PB.mul (PB.const cE) (PB.pow (PB.add hbp (PB.const 1) (fun _ => le_refl _)) (kE + 1) (fun _ => le_refl _))
    (fun _ => le_refl _)

theorem stageCost_pb {base : Request → ℕ} (hbp : PB a base) (V : KeyVec a 9 (cursorOuts a base)) (cE kE : ℕ) :
    PB a (stageCost V cE kE) := by
  have hV : PB a V.cost := PB.of_le _ _ V.cost_le
  have hE := Ev_pb hbp cE kE
  have hW := width_pb (a := a)
  have hm : PB a (fun r => (base r + 1 + 10) ^ (kE + 1)) :=
    PB.pow (PB.add hbp (PB.const 11) (fun _ => le_refl _)) (kE + 1) (fun _ => le_refl _)
  have hN : PB a (fun r => (cE + 10) * (base r + 1 + 10) ^ (kE + 1)) := PB.mul (PB.const _) hm (fun _ => le_refl _)
  have hC : PB a (fun r => 8 * (8 * PacketsConstruction.fieldWidth a r + 10)) :=
    PB.mul (PB.const 8) (PB.add (PB.mul (PB.const 8) hW (fun _ => le_refl _)) (PB.const 10) (fun _ => le_refl _))
      (fun _ => le_refl _)
  have s1 := PB.add (PB.add (PB.mul (PB.const 2) hV (fun _ => le_refl _)) (PB.mul (PB.const 11) hE (fun _ => le_refl _))
    (fun _ => le_refl _)) (PB.add (PB.add hN hC (fun _ => le_refl _)) (PB.add (PB.mul (PB.const 2) hbp (fun _ => le_refl _))
      (PB.const 40) (fun _ => le_refl _)) (fun _ => le_refl _)) (fun _ => le_refl _)
  refine PB.mono s1 (fun r => ?_)
  have hn := PacketsGlue.Nest.cost_le cE (base r + 1) (kE + 1)
  have hcc := chainCost_le (PacketsConstruction.fieldWidth a r) (chainOf r)
  have hl := chainOf_length r
  have hcc' : chainCost (PacketsConstruction.fieldWidth a r) (chainOf r) ≤
      8 * (8 * PacketsConstruction.fieldWidth a r + 10) :=
    hcc.trans (Nat.mul_le_mul_right _ (by omega))
  have hEv : cE * (base r + 1) ^ (kE + 1) = Ev cE kE base r := rfl
  unfold stageCost PacketsGlue.DriverPhase.cost
  rw [hEv]
  omega

/-- **The row-key cursor**, from the per-circuit bound stages `cb` and a base stage above `smallSize`. -/
theorem cursorFam_nonempty (cb : ∀ i : Fin 4, UnaryStage a (circBound a i.val)) {base : Request → ℕ}
    (baseS : UnaryStage a base) (hsb : ∀ r, r.smallSize a ≤ base r) (hbp : PB a base) : Nonempty (CursorFam a) := by
  let V := flagVec cb baseS
  have hX : PB a (fun r => 2 * V.cost r + 2 * PacketsConstruction.fieldWidth a r + 3) :=
    PB.add (PB.add (PB.mul (PB.const 2) (PB.of_le _ _ V.cost_le) (fun _ => le_refl _))
      (PB.mul (PB.const 2) (width_pb (a := a)) (fun _ => le_refl _)) (fun _ => le_refl _)) (PB.const 3)
      (fun _ => le_refl _)
  obtain ⟨cX, dX, hXb⟩ := hX
  have hE : ∀ r, base r + 2 ≤ Ev (cX + 2) dX base r ∧ 2 * V.cost r + 3 ≤ Ev (cX + 2) dX base r ∧
      2 * PacketsConstruction.fieldWidth a r + 1 ≤ Ev (cX + 2) dX base r := by
    intro r
    have hs := hsb r
    have h1 : base r + 1 ≤ (base r + 1) ^ (dX + 1) := Nat.le_self_pow (by omega) _
    have h2 : (r.smallSize a) ^ dX ≤ (base r + 1) ^ (dX + 1) :=
      (Nat.pow_le_pow_left (by omega) dX).trans (Nat.pow_le_pow_right (by omega) (by omega))
    have h3 := Nat.mul_le_mul_left cX h2
    have hx : 2 * V.cost r + 2 * PacketsConstruction.fieldWidth a r + 3 ≤ cX * (r.smallSize a) ^ dX := hXb r
    have e : Ev (cX + 2) dX base r = cX * (base r + 1) ^ (dX + 1) + 2 * (base r + 1) ^ (dX + 1) := by
      unfold Ev; ring
    rw [e]
    refine ⟨by omega, by omega, by omega⟩
  obtain ⟨cC, dC, hC⟩ := stageCost_pb hbp V (cX + 2) dX
  have hneed : PB a (fun r => Ev (cX + 2) dX base r + 1) :=
    PB.add (Ev_pb hbp (cX + 2) dX) (PB.const 1) (fun _ => le_refl _)
  exact ⟨{
    u := TS V.extra dX - 9
    need := fun r => Ev (cX + 2) dX base r + 1
    need_pb := hneed
    cursor := fun w R cR dR hR hu hn =>
      cursorAt V (cX + 2) dX cC dC hC hE w R cR dR hR (by omega) hn }⟩

end
end NearCubicWires.PacketsConstruction.Cursor

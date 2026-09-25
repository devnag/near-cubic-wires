import Proof.Packets.PacketsDriverPhase
import Proof.Packets.PacketsSetup

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.BlockPlatform NearCubicWires.PacketsConstruction
noncomputable section

/-! ## The ten words -/

section VecR
variable (a : DecompositionAlgorithm) (WS : UnaryStage a (fieldWidth a))
  (rowsS : UnaryStage a (fun r => (r.family a).rows.length)) {base : Request → ℕ} (baseS : UnaryStage a base)

/-- `1^(base+1)`: the loop counters' length. -/
def mStage : UnaryStage a (fun r => base r + 1) := baseS.thenMapP (plusMap 1) 6 1 (plus_cost 1)

/-- **The ten setup words**, one fixed machine (no scrub driver among them). -/
def setupVecR :=
  (VecStage.nil a (fun _ _ => [])).snoc (zeroW a WS) |>.snoc (zeroW a WS) |>.snoc (zeroW a WS)
    |>.snoc (zeroW a WS) |>.snoc (zeroW a WS) |>.snoc (zeroW a WS) |>.snoc (zeroW a WS)
    |>.snoc (flagW a WS rowsS) |>.snoc (rowW a rowsS) |>.snoc (mStage a baseS).toWord

/-- **The masked ten-word run**, with its words and a length bound on every tape. -/
theorem local_runR (r : Request) : ∃ A2 : Fin (11 + (setupVecR a WS rowsS baseS).extra + 1) → List Bool,
    Step (MaskedReset.machine (setupVecR a WS rowsS baseS).machine (fun _ => true))
      (2 * (setupVecR a WS rowsS baseS).cost r + 2) (fun _ => 0)
      (Fin.addCases (motive := fun _ => List Bool)
        (inBank (11 + (setupVecR a WS rowsS baseS).extra) (Request.input a r)) (fun _ : Fin 1 => [])) (fun _ => 0) A2 ∧
    A2 ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r) ∧
    (∀ j (hj : 1 ≤ j ∧ j ≤ 7), A2 ⟨j, by omega⟩ = RepairOrdinary.frame (SignedSortKey.binary (fieldWidth a r) 0)) ∧
    A2 ⟨8, by omega⟩ = RepairOrdinary.frame (SignedSortKey.binary (fieldWidth a r)
      (if (r.family a).rows.length = 0 then 1 else 0)) ∧
    A2 ⟨9, by omega⟩ = RepairSource.VerifierDecoding.CompareMachine.word ((r.family a).rows.length) ∧
    A2 ⟨10, by omega⟩ = List.replicate (base r + 1) true ∧
    ∀ j, (A2 j).length ≤ 2 * (Request.input a r).length + 1 + (2 * (setupVecR a WS rowsS baseS).cost r + 2) + 1 := by
  obtain ⟨H1, A1, hV, a0, _, hout⟩ := (setupVecR a WS rowsS baseS).run r
  obtain ⟨k, hm⟩ := step_mask0 hV (fun _ => true) (by intro i _; rfl)
  refine ⟨Fin.addCases (motive := fun _ => List Bool) A1 (fun _ : Fin 1 => List.replicate k false), ?_, ?_⟩
  · refine (hm.congr_in ?_ rfl).congr ?_ rfl
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  have hl : ∀ j (hj : j < 11 + (setupVecR a WS rowsS baseS).extra),
      Fin.addCases (motive := fun _ => List Bool) A1 (fun _ : Fin 1 => List.replicate k false) ⟨j, by omega⟩ =
        A1 ⟨j, hj⟩ := by
    intro j hj
    show Fin.addCases (motive := fun _ => List Bool) A1 _ (Fin.castAdd 1 ⟨j, hj⟩) = _
    rw [Fin.addCases_left]
  have hWpos : 1 ≤ fieldWidth a r := by
    change 1 ≤ Nat.log 2 (digitBound a r) + 1
    omega
  refine ⟨by rw [hl 0 (by omega)]; exact a0, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [hl j (by omega)]
    rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with e | e | e | e | e | e | e <;>
      subst e
    · exact (hout 0 (by omega)).1
    · exact (hout 1 (by omega)).1
    · exact (hout 2 (by omega)).1
    · exact (hout 3 (by omega)).1
    · exact (hout 4 (by omega)).1
    · exact (hout 5 (by omega)).1
    · exact (hout 6 (by omega)).1
  · rw [hl 8 (by omega), (hout 7 (by omega)).1]
    exact flag_word _ _ (by split_ifs <;> omega) hWpos
  · rw [hl 9 (by omega)]; exact (hout 8 (by omega)).1
  · rw [hl 10 (by omega)]; exact (hout 9 (by omega)).1
  · obtain ⟨res, hres, _, ht, hs⟩ := hm
    have hsup := RecoveryTapeSupport.run_support _ _ _ res hres (RepairOrdinary.frame (Request.input a r)).length 0
      (fun i => by refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp)
      (by
        intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp only [Fin.addCases_left]
          rw [inBank_val]; split_ifs <;> simp
        · simp)
    intro j
    have h1 := hsup j
    rw [ht] at h1
    refine h1.trans ?_
    rw [frame_length]
    apply max_le <;> omega

end VecR

/-! ## Slots -/

/-- The vector: 0 input, 1–8 digit words onto 2–9, 9 the row count onto `12+w`, `10..11+E` onto scratch `10..11+E`. -/
def σR (w E : ℕ) (hE : E + 2 ≤ w) (j : Fin (11 + E + 1)) : Fin (10 + w + 2 + 1) :=
  if j.val = 0 then ⟨0, by omega⟩
  else if j.val ≤ 8 then ⟨j.val + 1, by omega⟩
  else if j.val = 9 then ⟨10 + w + 2, by omega⟩
  else ⟨j.val, by have := j.isLt; omega⟩

theorem σR_val (w E : ℕ) (hE : E + 2 ≤ w) (j : Fin (11 + E + 1)) : (σR w E hE j).val =
    if j.val = 0 then 0 else if j.val ≤ 8 then j.val + 1 else if j.val = 9 then 10 + w + 2 else j.val := by
  unfold σR; split_ifs <;> rfl

theorem σR_inj (w E : ℕ) (hE : E + 2 ≤ w) : Function.Injective (σR w E hE) := by
  intro x y h
  have hv := congrArg Fin.val h
  rw [σR_val, σR_val] at hv
  have := x.isLt
  have := y.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The driver phase: log, driver, source (scratch 10), counters (scratch `12+E..`). -/
def δR (w E k : ℕ) (hk : E + k + 4 ≤ w) (j : Fin (4 + k)) : Fin (10 + w + 2 + 1) :=
  if j.val = 0 then ⟨10 + w, by omega⟩
  else if j.val = 1 then ⟨10 + w + 1, by omega⟩
  else if j.val = 2 then ⟨10, by omega⟩
  else ⟨j.val + 9 + E, by have := j.isLt; omega⟩

theorem δR_val (w E k : ℕ) (hk : E + k + 4 ≤ w) (j : Fin (4 + k)) : (δR w E k hk j).val =
    if j.val = 0 then 10 + w else if j.val = 1 then 10 + w + 1 else if j.val = 2 then 10 else j.val + 9 + E := by
  unfold δR; split_ifs <;> rfl

theorem δR_inj (w E k : ℕ) (hk : E + k + 4 ≤ w) : Function.Injective (δR w E k hk) := by
  intro x y h
  have hv := congrArg Fin.val h
  rw [δR_val, δR_val] at hv
  have := x.isLt
  have := y.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The install through `σR`, by value. -/
theorem inst_σR (w E : ℕ) (hE : E + 2 ≤ w) (B : Fin (10 + w + 2 + 1) → List Bool)
    (A : Fin (11 + E + 1) → List Bool) (i : Fin (10 + w + 2 + 1)) :
    install (σR w E hE) B A i =
      if h0 : i.val = 0 then A ⟨0, by omega⟩
      else if h1 : 2 ≤ i.val ∧ i.val ≤ 9 then A ⟨i.val - 1, by omega⟩
      else if h2 : i.val = 10 + w + 2 then A ⟨9, by omega⟩
      else if h3 : 10 ≤ i.val ∧ i.val ≤ 11 + E then A ⟨i.val, by omega⟩
      else B i := by
  have hs : ∀ j : Fin (11 + E + 1), σR w E hE j = i → install (σR w E hE) B A i = A j := by
    intro j hj; subst hj; exact install_slot _ (σR_inj w E hE) _ _ j
  split_ifs with h0 h1 h2 h3
  · exact hs _ (Fin.ext (by rw [σR_val]; simp [h0]))
  · exact hs _ (Fin.ext (by
      rw [σR_val]; simp only [Fin.val_mk]; rw [if_neg (by omega), if_pos (by omega)]; omega))
  · exact hs _ (Fin.ext (by rw [σR_val]; simp [h2]))
  · exact hs _ (Fin.ext (by
      rw [σR_val]; simp only [Fin.val_mk]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]))
  · apply install_other
    intro j hj
    have hv := congrArg Fin.val hj
    rw [σR_val] at hv
    have := j.isLt
    have := i.isLt
    split_ifs at hv <;> omega

/-- The install through `δR`, by value. -/
theorem inst_δR (w E k : ℕ) (hk : E + k + 4 ≤ w) (B : Fin (10 + w + 2 + 1) → List Bool)
    (T : Fin (4 + k) → List Bool) (i : Fin (10 + w + 2 + 1)) :
    install (δR w E k hk) B T i =
      if h0 : i.val = 10 + w then T ⟨0, by omega⟩
      else if h1 : i.val = 10 + w + 1 then T ⟨1, by omega⟩
      else if h2 : i.val = 10 then T ⟨2, by omega⟩
      else if h3 : 12 + E ≤ i.val ∧ i.val ≤ 12 + E + k then T ⟨i.val - 9 - E, by omega⟩
      else B i := by
  have hs : ∀ j : Fin (4 + k), δR w E k hk j = i → install (δR w E k hk) B T i = T j := by
    intro j hj; subst hj; exact install_slot _ (δR_inj w E k hk) _ _ j
  split_ifs with h0 h1 h2 h3
  · exact hs _ (Fin.ext (by rw [δR_val]; simp [h0]))
  · exact hs _ (Fin.ext (by rw [δR_val]; simp [h1]))
  · exact hs _ (Fin.ext (by rw [δR_val]; simp [h2]))
  · exact hs _ (Fin.ext (by rw [δR_val]; simp; split_ifs <;> omega))
  · apply install_other
    intro j hj
    have hv := congrArg Fin.val hj
    rw [δR_val] at hv
    have := j.isLt
    have := i.isLt
    split_ifs at hv <;> omega

end
end NearCubicWires.PacketsGlue.RequestMeta

/-! ## The machine and its run -/

namespace NearCubicWires.PacketsGlue.Nest

theorem cost_le (c m : ℕ) : ∀ j : ℕ, cost c m j + 10 ≤ (c + 10) * (m + 10) ^ j := by
  intro j
  induction j with
  | zero => simp [cost]
  | succ j ih =>
    have h1 : cost c m (j + 1) + 10 ≤ (m + 10) * (cost c m j + 10) := by
      show 1 + 1 + ((m * (cost c m j + 3) + 3) + 1 + 1) + 10 ≤ _
      nlinarith
    calc cost c m (j + 1) + 10 ≤ (m + 10) * (cost c m j + 10) := h1
      _ ≤ (m + 10) * ((c + 10) * (m + 10) ^ j) := Nat.mul_le_mul_left _ ih
      _ = (c + 10) * (m + 10) ^ (j + 1) := by ring

end NearCubicWires.PacketsGlue.Nest

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.BlockPlatform NearCubicWires.PacketsConstruction
noncomputable section

section RunR
variable (a : DecompositionAlgorithm) (w : ℕ) (R : Request → ℕ) (cR dR : ℕ)
  (hR : ∀ r, R r ≤ cR * (r.smallSize a) ^ dR)
  (WS : UnaryStage a (fieldWidth a)) (rowsS : UnaryStage a (fun r => (r.family a).rows.length))
  {base : Request → ℕ} (baseS : UnaryStage a base) (c k : ℕ)

/-- **The setup machine** (one per `(w, c, k)`). -/
def setupMachineR (hw : (setupVecR a WS rowsS baseS).extra + k + 4 ≤ w) :=
  Composition.machine
    (Composition.machine
      (RecoveryFocus.machine (σR w (setupVecR a WS rowsS baseS).extra (by omega))
        (MaskedReset.machine (setupVecR a WS rowsS baseS).machine (fun _ => true)))
      (RecoveryFocus.machine (δR w (setupVecR a WS rowsS baseS).extra k hw) (DriverPhase.machine c k)))
    (Composition.machine
      (CloseoutWitness.SelectedErase.machine (scr w) ⟨10 + w + 1, by omega⟩ ⟨10 + w, by omega⟩)
      (MoveOne.machine (10 + w + 2 + 1) ⟨10 + w + 2, by omega⟩))

/-- The setup's fuel. -/
def setupCostR (r : Request) : ℕ :=
  (2 * (setupVecR a WS rowsS baseS).cost r + 2) + 1 + DriverPhase.cost c k (base r + 1) + 1 +
    ((2 * R r + 4) + 1 + 1)

theorem dock_entryR (E : ℕ) (hE : E + 2 ≤ w) (r : Request) (j : Fin (11 + E + 1)) :
    B0 a w R r (σR w E hE j) =
      Fin.addCases (motive := fun _ => List Bool) (inBank (11 + E) (Request.input a r)) (fun _ : Fin 1 => []) j := by
  rw [B0_val, ac2]
  have hv := σR_val w E hE j
  have := j.isLt
  by_cases h0 : j.val = 0
  · have hz : (σR w E hE j).val = 0 := by rw [hv, if_pos h0]
    rw [if_pos hz, dif_pos (by omega), inBank_val]
    simp only [Fin.val_mk, h0, if_true]
  · have hne0 : (σR w E hE j).val ≠ 0 := by rw [hv]; split_ifs <;> omega
    have hnel : (σR w E hE j).val ≠ 10 + w := by rw [hv]; split_ifs <;> omega
    rw [if_neg hne0, if_neg hnel]
    by_cases hlt : j.val < 11 + E
    · rw [dif_pos hlt, inBank_val]
      simp only [Fin.val_mk, h0, if_false]
    · rw [dif_neg hlt]

theorem inst_σR_out (E : ℕ) (hE : E + 2 ≤ w) (B : Fin (10 + w + 2 + 1) → List Bool) (A : Fin (11 + E + 1) → List Bool)
    (i : Fin (10 + w + 2 + 1)) (h0 : i.val ≠ 0) (h1 : ¬(2 ≤ i.val ∧ i.val ≤ 9)) (h2 : i.val ≠ 10 + w + 2)
    (h3 : ¬(10 ≤ i.val ∧ i.val ≤ 11 + E)) : install (σR w E hE) B A i = B i := by
  rw [inst_σR, dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3]

theorem inst_σR_scr (E : ℕ) (hE : E + 2 ≤ w) (B : Fin (10 + w + 2 + 1) → List Bool) (A : Fin (11 + E + 1) → List Bool)
    (i : Fin (10 + w + 2 + 1)) (h3 : 10 ≤ i.val ∧ i.val ≤ 11 + E) :
    install (σR w E hE) B A i = A ⟨i.val, by omega⟩ := by
  rw [inst_σR, dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos h3]

theorem entry_eqR (E : ℕ) (hw : E + k + 4 ≤ w) (r : Request) (A2 : Fin (11 + E + 1) → List Bool)
    (hU : A2 ⟨10, by omega⟩ = List.replicate (base r + 1) true) (hRr : R r = c * (base r + 1) ^ (k + 1))
    (j : Fin (4 + k)) :
    install (σR w E (by omega)) (B0 a w R r) A2 (δR w E k hw j) =
      DriverPhase.entryA k (base r + 1) (c * (base r + 1) ^ (k + 1)) j := by
  have hv := δR_val w E k hw j
  have := j.isLt
  unfold DriverPhase.entryA
  by_cases h0 : j.val = 0
  · have e : (δR w E k hw j).val = 10 + w := by rw [hv, if_pos h0]
    rw [inst_σR_out w E (by omega) _ _ _ (by omega) (by omega) (by omega) (by omega), B0_val, if_neg (by omega),
      if_pos e, if_pos h0, hRr]
  · by_cases h1 : j.val = 1
    · have e : (δR w E k hw j).val = 10 + w + 1 := by rw [hv, if_neg h0, if_pos h1]
      rw [inst_σR_out w E (by omega) _ _ _ (by omega) (by omega) (by omega) (by omega), B0_val, if_neg (by omega),
        if_neg (by omega), if_neg h0, if_neg (by omega)]
    · by_cases h2 : j.val = 2
      · have e : (δR w E k hw j).val = 10 := by rw [hv, if_neg h0, if_neg h1, if_pos h2]
        rw [inst_σR_scr w E (by omega) _ _ _ (by omega), if_neg h0, if_pos h2]
        have e2 : (⟨(δR w E k hw j).val, by omega⟩ : Fin (11 + E + 1)) = ⟨10, by omega⟩ := Fin.ext e
        rw [e2, hU]
      · have e : (δR w E k hw j).val = j.val + 9 + E := by rw [hv, if_neg h0, if_neg h1, if_neg h2]
        rw [inst_σR_out w E (by omega) _ _ _ (by omega) (by omega) (by omega) (by omega), B0_val, if_neg (by omega),
          if_neg (by omega), if_neg h0, if_neg h2]

theorem exitA_log (k m R' : ℕ) : DriverPhase.exitA k m R' ⟨0, by omega⟩ = List.replicate (R' + 1) false := by
  simp [DriverPhase.exitA]

theorem exitA_drv (k m R' : ℕ) : DriverPhase.exitA k m R' ⟨1, by omega⟩ = List.replicate R' true := by
  simp [DriverPhase.exitA]

theorem m_le_R (b c k : ℕ) (hc : 2 ≤ c) : b + 1 + 1 ≤ c * (b + 1) ^ (k + 1) := by
  have h1 : b + 1 ≤ (b + 1) ^ (k + 1) := Nat.le_self_pow (by omega) _
  have h2 : 2 * (b + 1) ≤ c * (b + 1) ^ (k + 1) := Nat.mul_le_mul hc h1
  omega

theorem exit_eqR (E : ℕ) (hw : E + k + 4 ≤ w) (r : Request) (A2 : Fin (11 + E + 1) → List Bool)
    (hA0 : A2 ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r))
    (hZ : ∀ j (hj : 1 ≤ j ∧ j ≤ 7), A2 ⟨j, by omega⟩ = RepairOrdinary.frame (SignedSortKey.binary (fieldWidth a r) 0))
    (hF : A2 ⟨8, by omega⟩ = RepairOrdinary.frame (SignedSortKey.binary (fieldWidth a r)
      (if (r.family a).rows.length = 0 then 1 else 0)))
    (hC : A2 ⟨9, by omega⟩ = RepairSource.VerifierDecoding.CompareMachine.word ((r.family a).rows.length))
    (hRr : R r = c * (base r + 1) ^ (k + 1)) :
    Scrub.blank (scr w) (install (δR w E k hw) (install (σR w E (by omega)) (B0 a w R r) A2)
      (DriverPhase.exitA k (base r + 1) (c * (base r + 1) ^ (k + 1)))) (R r) = goalVal a w R r := by
  funext i
  have := i.isLt
  simp only [Scrub.blank, scr]
  by_cases hs : 10 ≤ i.val ∧ i.val < 10 + w
  · rw [if_pos (by simpa using hs), gvS a w R r i hs]
  · rw [if_neg (by simpa using hs), inst_δR]
    by_cases hL : i.val = 10 + w
    · rw [dif_pos hL, gvL a w R r i hL, exitA_log, hRr]
    · rw [dif_neg hL]
      by_cases hD : i.val = 10 + w + 1
      · rw [dif_pos hD, gvD a w R r i hD, exitA_drv, hRr]
      · rw [dif_neg hD, dif_neg (by omega), dif_neg (by omega), inst_σR]
        by_cases h0 : i.val = 0
        · rw [dif_pos h0, gv0 a w R r i h0]; exact hA0
        · rw [dif_neg h0]
          by_cases h1 : 2 ≤ i.val ∧ i.val ≤ 9
          · rw [dif_pos h1]
            by_cases h9 : i.val = 9
            · rw [gv9 a w R r i h9]
              have e : (⟨i.val - 1, by omega⟩ : Fin (11 + E + 1)) = ⟨8, by omega⟩ := Fin.ext (by simp; omega)
              rw [e]; exact hF
            · rw [gvZ a w R r i ⟨h1.1, by omega⟩]; exact hZ (i.val - 1) (by omega)
          · rw [dif_neg h1]
            by_cases hC' : i.val = 10 + w + 2
            · rw [dif_pos hC', gvC a w R r i hC']; exact hC
            · rw [dif_neg hC', dif_neg (by omega), B0_val, if_neg h0, if_neg hL]
              rw [gv1 a w R r i (by omega)]

theorem lens_R (E : ℕ) (hw : E + k + 4 ≤ w) (r : Request) (A2 : Fin (11 + E + 1) → List Bool) (L : ℕ)
    (hlen : ∀ j, (A2 j).length ≤ L) (hL : L ≤ R r) (hRr : R r = c * (base r + 1) ^ (k + 1)) (hc : 2 ≤ c) :
    ∀ i, scr w i = true → (install (δR w E k hw) (install (σR w E (by omega)) (B0 a w R r) A2)
      (DriverPhase.exitA k (base r + 1) (c * (base r + 1) ^ (k + 1))) i).length ≤ R r := by
  intro i hi
  simp only [scr, decide_eq_true_eq] at hi
  have hm := m_le_R (base r) c k hc
  rw [inst_δR, dif_neg (by omega), dif_neg (by omega)]
  by_cases h2 : i.val = 10
  · rw [dif_pos h2]; simp [DriverPhase.exitA]; omega
  · rw [dif_neg h2]
    by_cases h3 : 12 + E ≤ i.val ∧ i.val ≤ 12 + E + k
    · rw [dif_pos h3]
      simp only [DriverPhase.exitA, Fin.val_mk]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp [RepairSource.VerifierDecoding.CompareMachine.word]; omega
    · rw [dif_neg h3, inst_σR, dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
      by_cases h4 : 10 ≤ i.val ∧ i.val ≤ 11 + E
      · rw [dif_pos h4]; exact (hlen _).trans hL
      · rw [dif_neg h4, B0_val, if_neg (by omega), if_neg (by omega)]; simp

/-- **The setup run**: from the padded input to the loop's first cell. -/
theorem setup_runR (hw : (setupVecR a WS rowsS baseS).extra + k + 4 ≤ w)
    (hRdef : ∀ r, R r = c * (base r + 1) ^ (k + 1)) (hc : 2 ≤ c)
    (hneed : ∀ r, 2 * (Request.input a r).length + 2 * (setupVecR a WS rowsS baseS).cost r + 5 ≤ R r)
    (r : Request) :
    Step (setupMachineR a w WS rowsS baseS c k hw) (setupCostR a R WS rowsS baseS c k r) (fun _ => 0)
      (fun i => ZeroPadding.pad (setupBlank w R r i) (inBank (10 + w + 2 + 1) (Request.input a r) i))
      (Fin.addCases (Fin.addCases ((digitLayout a w R cR dR hR).heads [])
        ((blockScrubForm (10 + w) (digitLayout a w R cR dR hR).scratch).residentH (R r))) (fun _ : Fin 1 => 1))
      (Fin.addCases (Fin.addCases ((digitLayout a w R cR dR hR).bank r (rcKeys a r)[0]? [])
        ((blockScrubForm (10 + w) (digitLayout a w R cR dR hR).scratch).residentA (R r)))
        (fun _ : Fin 1 => RepairSource.VerifierDecoding.CompareMachine.word (rcKeys a r).length)) := by
  obtain ⟨A2, hm, hA0, hZ, hF, hC, hU, hlen⟩ := local_runR a WS rowsS baseS r
  have hRr := hRdef r
  have hn := hneed r
  have d1 := hm.dock (σR w (setupVecR a WS rowsS baseS).extra (by omega)) (σR_inj w _ (by omega)) (fun _ => 0)
    (B0 a w R r) (fun _ => rfl) (fun j => dock_entryR a w R _ (by omega) r j)
  rw [dockH_zero] at d1
  have dP := (DriverPhase.run c k (base r + 1)).dock (δR w (setupVecR a WS rowsS baseS).extra k hw)
    (δR_inj w _ k hw) (fun _ => 0) _ (fun _ => rfl) (fun j => entry_eqR a w R c k _ hw r A2 hU hRr j)
  rw [dockH_zero] at dP
  have hb := lens_R a w R c k _ hw r A2 _ hlen (by omega) hRr hc
  have hdrv : install (δR w (setupVecR a WS rowsS baseS).extra k hw)
      (install (σR w (setupVecR a WS rowsS baseS).extra (by omega)) (B0 a w R r) A2)
      (DriverPhase.exitA k (base r + 1) (c * (base r + 1) ^ (k + 1))) ⟨10 + w + 1, by omega⟩ =
        List.replicate (R r) true := by
    rw [inst_δR, dif_neg (by simp), dif_pos rfl, exitA_drv, hRr]
  have hlog : install (δR w (setupVecR a WS rowsS baseS).extra k hw)
      (install (σR w (setupVecR a WS rowsS baseS).extra (by omega)) (B0 a w R r) A2)
      (DriverPhase.exitA k (base r + 1) (c * (base r + 1) ^ (k + 1))) ⟨10 + w, by omega⟩ =
        List.replicate (R r + 1) false := by
    rw [inst_δR, dif_pos rfl, exitA_log, hRr]
  have d2 := Scrub.erase_step (scr w) ⟨10 + w + 1, by omega⟩ ⟨10 + w, by omega⟩ (by simp [scr])
    (by simp [scr]) (by simp) (R r) (R r + 1) (le_refl _) (fun _ => 0) _ (fun _ _ => rfl) hb hdrv hlog
  have d3 := MoveOne.run (10 + w + 2 + 1) ⟨10 + w + 2, by omega⟩ (fun _ => 0)
    (Scrub.blank (scr w) (install (δR w (setupVecR a WS rowsS baseS).extra k hw)
      (install (σR w (setupVecR a WS rowsS baseS).extra (by omega)) (B0 a w R r) A2)
      (DriverPhase.exitA k (base r + 1) (c * (base r + 1) ^ (k + 1)))) (R r))
  refine ((d1.seq dP).seq (d2.seq d3)).congr ?_ ?_
  · funext i
    rw [ac3]
    by_cases hi : i = ⟨10 + w + 2, by omega⟩
    · subst hi
      simp
    · rw [Function.update_of_ne hi]
      have hv : i.val ≠ 10 + w + 2 := fun h => hi (Fin.ext h)
      have := i.isLt
      split_ifs <;> first | omega | simp [Layout.heads, digitLayout, blockScrubForm]
  · rw [exit_eqR a w R c k _ hw r A2 hA0 hZ hF hC hRr, target_eq a w R cR dR hR r]

/-- The setup's cost coefficient and degree. -/
def setupCoefR (baseC : ℕ) : ℕ :=
  2 * (setupVecR a WS rowsS baseS).coefficient + 2 * baseC + (c + 10) * (baseC + 11) ^ (k + 1) + 5 * cR + 30

def setupDegR (baseD : ℕ) : ℕ := (setupVecR a WS rowsS baseS).degree + baseD * (k + 1) + dR + baseD

include hR in
theorem setupCostR_le (baseC baseD : ℕ) (hbase : ∀ r, base r ≤ baseC * (r.smallSize a) ^ baseD)
    (hRdef : ∀ r, R r = c * (base r + 1) ^ (k + 1)) (r : Request) :
    setupCostR a R WS rowsS baseS c k r ≤
      setupCoefR a cR WS rowsS baseS c k baseC * (r.smallSize a) ^ setupDegR a dR WS rowsS baseS k baseD := by
  have hV := (setupVecR a WS rowsS baseS).cost_le r
  have hb := hbase r
  have hRb := hR r
  have hS : 1 ≤ r.smallSize a := one_le_small a r
  set S := r.smallSize a with hSdef
  set Dg := setupDegR a dR WS rowsS baseS k baseD with hDg
  have pV : S ^ (setupVecR a WS rowsS baseS).degree ≤ S ^ Dg := pow_le_pow_small a r _ _ (by rw [hDg]; unfold setupDegR; omega)
  have pB : S ^ baseD ≤ S ^ Dg := pow_le_pow_small a r _ _ (by rw [hDg]; unfold setupDegR; omega)
  have pBk : S ^ (baseD * (k + 1)) ≤ S ^ Dg := pow_le_pow_small a r _ _ (by rw [hDg]; unfold setupDegR; omega)
  have pR : S ^ dR ≤ S ^ Dg := pow_le_pow_small a r _ _ (by rw [hDg]; unfold setupDegR; omega)
  have p1 : 1 ≤ S ^ Dg := Nat.one_le_pow _ _ hS
  have pb1 : 1 ≤ S ^ baseD := Nat.one_le_pow _ _ hS
  have hRr := hRdef r
  have hN := Nest.cost_le c (base r + 1) (k + 1)
  have hm10 : base r + 1 + 10 ≤ (baseC + 11) * S ^ baseD := by nlinarith
  have hpow : (base r + 1 + 10) ^ (k + 1) ≤ (baseC + 11) ^ (k + 1) * S ^ (baseD * (k + 1)) := by
    calc (base r + 1 + 10) ^ (k + 1) ≤ ((baseC + 11) * S ^ baseD) ^ (k + 1) := Nat.pow_le_pow_left hm10 _
      _ = (baseC + 11) ^ (k + 1) * S ^ (baseD * (k + 1)) := by rw [mul_pow, ← pow_mul]
  have q1 := Nat.mul_le_mul_left ((setupVecR a WS rowsS baseS).coefficient) pV
  have q2 := Nat.mul_le_mul_left baseC pB
  have q3 := Nat.mul_le_mul_left (c + 10) hpow
  have q4 := Nat.mul_le_mul_left ((c + 10) * (baseC + 11) ^ (k + 1)) pBk
  have q5 := Nat.mul_le_mul_left cR pR
  have hRX : R r ≤ cR * S ^ Dg := hRb.trans q5
  have hNX : Nest.cost c (base r + 1) (k + 1) ≤ (c + 10) * (baseC + 11) ^ (k + 1) * S ^ Dg := by
    have e : (c + 10) * ((baseC + 11) ^ (k + 1) * S ^ (baseD * (k + 1))) =
        (c + 10) * (baseC + 11) ^ (k + 1) * S ^ (baseD * (k + 1)) := by ring
    omega
  unfold setupCostR DriverPhase.cost setupCoefR
  rw [← hRr]
  have e : (2 * (setupVecR a WS rowsS baseS).coefficient + 2 * baseC + (c + 10) * (baseC + 11) ^ (k + 1) +
      5 * cR + 30) * S ^ Dg = 2 * ((setupVecR a WS rowsS baseS).coefficient * S ^ Dg) + 2 * (baseC * S ^ Dg) +
      (c + 10) * (baseC + 11) ^ (k + 1) * S ^ Dg + 5 * (cR * S ^ Dg) + 30 * S ^ Dg := by ring
  rw [e]
  omega

/-- **The packets setup at `digitLayout`, room satisfiable**: scrub width `R r = c·(base r+1)^(k+1)`, `c ≥ 2`, scratch
count `w ≥ vec.extra + k + 4`, and every scratch length bounded by `need r = 2|input| + 2·vec.cost + 5 ≤ R r`. -/
def setupPGR (baseC baseD : ℕ) (hbase : ∀ r, base r ≤ baseC * (r.smallSize a) ^ baseD)
    (hw : (setupVecR a WS rowsS baseS).extra + k + 4 ≤ w)
    (hRdef : ∀ r, R r = c * (base r + 1) ^ (k + 1)) (hc : 2 ≤ c)
    (hneed : ∀ r, 2 * (Request.input a r).length + 2 * (setupVecR a WS rowsS baseS).cost r + 5 ≤ R r) :
    Setup (digitLayout a w R cR dR hR) (blockScrubForm (10 + w) (digitLayout a w R cR dR hR).scratch) where
  states := _
  machine := setupMachineR a w WS rowsS baseS c k hw
  cost := setupCostR a R WS rowsS baseS c k
  coefficient := setupCoefR a cR WS rowsS baseS c k baseC
  degree := setupDegR a dR WS rowsS baseS k baseD
  cost_le := by
    intro r
    have h := setupCostR_le a R cR dR hR WS rowsS baseS c k baseC baseD hbase hRdef r
    have hx : setupCoefR a cR WS rowsS baseS c k baseC * (r.smallSize a) ^ setupDegR a dR WS rowsS baseS k baseD ≤
        setupCoefR a cR WS rowsS baseS c k baseC * ((r.family a).rows.length + 1) *
          (r.smallSize a) ^ setupDegR a dR WS rowsS baseS k baseD := by
      rw [Nat.mul_assoc]
      apply Nat.mul_le_mul_left
      exact Nat.le_mul_of_pos_left _ (by omega)
    exact h.trans hx
  blank := setupBlank w R
  blankOutput := by
    intro r
    unfold setupBlank
    have hv : ((((digitLayout a w R cR dR hR).output.castAdd
      (blockScrubForm (10 + w) (digitLayout a w R cR dR hR).scratch).extra).castAdd 1 : Fin _)).val = 1 := rfl
    rw [if_neg (by rw [hv]; omega)]
  run := fun r => setup_runR a w R cR dR hR WS rowsS baseS c k hw hRdef hc hneed r

end RunR

section Fam
variable (a : DecompositionAlgorithm) (WS : UnaryStage a (fieldWidth a))
  (rowsS : UnaryStage a (fun r => (r.family a).rows.length)) {base : Request → ℕ} (baseS : UnaryStage a base)

def needR (r : Request) : ℕ := 2 * (Request.input a r).length + 2 * (setupVecR a WS rowsS baseS).cost r + 5

theorem needR_le (r : Request) :
    needR a WS rowsS baseS r ≤
      (2 * (setupVecR a WS rowsS baseS).coefficient + 7) * (r.smallSize a) ^ ((setupVecR a WS rowsS baseS).degree + 1) := by
  have h1 := (setupVecR a WS rowsS baseS).cost_le r
  have h2 := input_le_small a r
  have hs := one_le_small a r
  have p1 : (r.smallSize a) ^ (setupVecR a WS rowsS baseS).degree ≤
      (r.smallSize a) ^ ((setupVecR a WS rowsS baseS).degree + 1) := pow_le_pow_small a r _ _ (by omega)
  have p2 : r.smallSize a ≤ (r.smallSize a) ^ ((setupVecR a WS rowsS baseS).degree + 1) := by
    calc r.smallSize a = (r.smallSize a) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_small a r _ _ (by omega)
  have q := Nat.mul_le_mul_left (setupVecR a WS rowsS baseS).coefficient p1
  unfold needR
  have e : (2 * (setupVecR a WS rowsS baseS).coefficient + 7) *
      (r.smallSize a) ^ ((setupVecR a WS rowsS baseS).degree + 1) =
      2 * ((setupVecR a WS rowsS baseS).coefficient * (r.smallSize a) ^ ((setupVecR a WS rowsS baseS).degree + 1)) +
        7 * (r.smallSize a) ^ ((setupVecR a WS rowsS baseS).degree + 1) := by ring
  rw [e]
  omega

def setupFamField (baseC baseD : ℕ) (hbase : ∀ r, base r ≤ baseC * (r.smallSize a) ^ baseD) :
    ∀ (w c D cR dR : ℕ) (hR : ∀ r, c * (base r + 1) ^ D ≤ cR * (r.smallSize a) ^ dR),
      2 ≤ c → 1 ≤ D → (setupVecR a WS rowsS baseS).extra + D + 3 ≤ w →
      (∀ r, needR a WS rowsS baseS r ≤ c * (base r + 1) ^ D) →
      Setup (digitLayout a w (fun r => c * (base r + 1) ^ D) cR dR hR)
        (blockScrubForm (10 + w) (digitLayout a w (fun r => c * (base r + 1) ^ D) cR dR hR).scratch) :=
  fun w c D cR dR hR hc hD hw hn =>
    setupPGR a w (fun r => c * (base r + 1) ^ D) cR dR hR WS rowsS baseS c (D - 1) baseC baseD hbase (by omega)
      (fun r => by simp only [Nat.sub_add_cancel hD]) hc hn

end Fam

end
end NearCubicWires.PacketsGlue.RequestMeta


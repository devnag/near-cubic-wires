import Proof.Rows.RowsHeaderWMinParts

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsHeaderW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation NearCubicWires.P1Closure
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.PacketsGlue.RequestMeta
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

/-! ## 1. The local port maps (values; `x`, `y` = the extras of `nStage`, `bStage`) -/

def mN (i : ℕ) : ℕ := if i = 0 then 0 else i + 3
def mB (x i : ℕ) : ℕ := if i = 0 then 0 else if i = 1 then 6 + x else 5 + x + i
def mU (x y i : ℕ) : ℕ := if i = 0 then 1 else if i = 1 then 8 + x + y else 9 + x + y
def mK (x y i : ℕ) : ℕ := if i = 0 then 8 + x + y else if i = 5 then 14 + x + y else 9 + x + y + i
def mC1 (x y i : ℕ) : ℕ :=
  if i = 0 then 14 + x + y else if i = 1 then 6 + x else if i = 2 then 17 + x + y else 18 + x + y
def mR (x y i : ℕ) : ℕ :=
  if i = 0 then 8 + x + y else if i = 12 then 30 + x + y else if i = 14 then 32 + x + y else 18 + x + y + i
def mC2 (x y i : ℕ) : ℕ :=
  if i = 0 then 32 + x + y else if i = 1 then 4 else if i = 2 then 34 + x + y else 35 + x + y
def mDd (x y i : ℕ) : ℕ := if i = 0 then 30 + x + y else if i = 1 then 3 else 36 + x + y
def mDn (x y i : ℕ) : ℕ := if i = 0 then 4 else if i = 1 then 3 else 36 + x + y

def RN (x v : ℕ) : Prop := v = 0 ∨ (4 ≤ v ∧ v ≤ 5 + x)
def RB (x y v : ℕ) : Prop := v = 0 ∨ (6 + x ≤ v ∧ v ≤ 7 + x + y)
def RU2 (x y v : ℕ) : Prop := v = 1 ∨ v = 8 + x + y ∨ v = 9 + x + y
def RK (x y v : ℕ) : Prop := v = 8 + x + y ∨ (10 + x + y ≤ v ∧ v ≤ 16 + x + y)
def RC1 (x y v : ℕ) : Prop := v = 14 + x + y ∨ v = 6 + x ∨ v = 17 + x + y ∨ v = 18 + x + y
def RR (x y v : ℕ) : Prop := v = 8 + x + y ∨ (19 + x + y ≤ v ∧ v ≤ 33 + x + y)
def RC2 (x y v : ℕ) : Prop := v = 32 + x + y ∨ v = 4 ∨ v = 34 + x + y ∨ v = 35 + x + y
def RD (x y v : ℕ) : Prop := v = 30 + x + y ∨ v = 4 ∨ v = 3 ∨ v = 36 + x + y

variable (x y : ℕ)

def slN : Fin (2 + x + 1) → Fin (4 + (33 + x + y)) := fun i =>
  ⟨mN i.val, by have := i.isLt; unfold mN; split_ifs <;> omega⟩
def slB : Fin (2 + y + 1) → Fin (4 + (33 + x + y)) := fun i =>
  ⟨mB x i.val, by have := i.isLt; unfold mB; split_ifs <;> omega⟩
def slU2 : Fin (2 + 1) → Fin (4 + (33 + x + y)) := fun i =>
  ⟨mU x y i.val, by have := i.isLt; unfold mU; split_ifs <;> omega⟩
def slK : Fin (7 + 1) → Fin (4 + (33 + x + y)) := fun i =>
  ⟨mK x y i.val, by have := i.isLt; unfold mK; split_ifs <;> omega⟩
def slC1 : Fin (3 + 1) → Fin (4 + (33 + x + y)) := fun i =>
  ⟨mC1 x y i.val, by have := i.isLt; unfold mC1; split_ifs <;> omega⟩
def slR2 : Fin (15 + 1) → Fin (4 + (33 + x + y)) := fun i =>
  ⟨mR x y i.val, by have := i.isLt; unfold mR; split_ifs <;> omega⟩
def slC2 : Fin (3 + 1) → Fin (4 + (33 + x + y)) := fun i =>
  ⟨mC2 x y i.val, by have := i.isLt; unfold mC2; split_ifs <;> omega⟩
def slDd : Fin 3 → Fin (4 + (33 + x + y)) := fun i =>
  ⟨mDd x y i.val, by have := i.isLt; unfold mDd; split_ifs <;> omega⟩
def slDn : Fin 3 → Fin (4 + (33 + x + y)) := fun i =>
  ⟨mDn x y i.val, by have := i.isLt; unfold mDn; split_ifs <;> omega⟩
def flag1 : Fin (4 + (33 + x + y)) := ⟨17 + x + y, by omega⟩
def flag2 : Fin (4 + (33 + x + y)) := ⟨34 + x + y, by omega⟩

theorem slN_inj : Function.Injective (slN x y) := by
  intro i j h
  have hv : mN i.val = mN j.val := congrArg Fin.val h
  have := i.isLt; have := j.isLt
  apply Fin.ext; unfold mN at hv; split_ifs at hv <;> omega
theorem slB_inj : Function.Injective (slB x y) := by
  intro i j h
  have hv : mB x i.val = mB x j.val := congrArg Fin.val h
  have := i.isLt; have := j.isLt
  apply Fin.ext; unfold mB at hv; split_ifs at hv <;> omega
theorem slU2_inj : Function.Injective (slU2 x y) := by
  intro i j h
  have hv : mU x y i.val = mU x y j.val := congrArg Fin.val h
  have := i.isLt; have := j.isLt
  apply Fin.ext; unfold mU at hv; split_ifs at hv <;> omega
theorem slK_inj : Function.Injective (slK x y) := by
  intro i j h
  have hv : mK x y i.val = mK x y j.val := congrArg Fin.val h
  have := i.isLt; have := j.isLt
  apply Fin.ext; unfold mK at hv; split_ifs at hv <;> omega
theorem slC1_inj : Function.Injective (slC1 x y) := by
  intro i j h
  have hv : mC1 x y i.val = mC1 x y j.val := congrArg Fin.val h
  have := i.isLt; have := j.isLt
  apply Fin.ext; unfold mC1 at hv; split_ifs at hv <;> omega
theorem slR2_inj : Function.Injective (slR2 x y) := by
  intro i j h
  have hv : mR x y i.val = mR x y j.val := congrArg Fin.val h
  have := i.isLt; have := j.isLt
  apply Fin.ext; unfold mR at hv; split_ifs at hv <;> omega
theorem slC2_inj : Function.Injective (slC2 x y) := by
  intro i j h
  have hv : mC2 x y i.val = mC2 x y j.val := congrArg Fin.val h
  have := i.isLt; have := j.isLt
  apply Fin.ext; unfold mC2 at hv; split_ifs at hv <;> omega
theorem slDd_inj : Function.Injective (slDd x y) := by
  intro i j h
  have hv : mDd x y i.val = mDd x y j.val := congrArg Fin.val h
  have := i.isLt; have := j.isLt
  apply Fin.ext; unfold mDd at hv; split_ifs at hv <;> omega
theorem slDn_inj : Function.Injective (slDn x y) := by
  intro i j h
  have hv : mDn x y i.val = mDn x y j.val := congrArg Fin.val h
  have := i.isLt; have := j.isLt
  apply Fin.ext; unfold mDn at hv; split_ifs at hv <;> omega

theorem slN_range (j : Fin (2 + x + 1)) : RN x (slN x y j).val := by
  have := j.isLt; show RN x (mN j.val); unfold RN mN; split_ifs <;> omega
theorem slB_range (j : Fin (2 + y + 1)) : RB x y (slB x y j).val := by
  have := j.isLt; show RB x y (mB x j.val); unfold RB mB; split_ifs <;> omega
theorem slU2_range (j : Fin (2 + 1)) : RU2 x y (slU2 x y j).val := by
  have := j.isLt; show RU2 x y (mU x y j.val); unfold RU2 mU; split_ifs <;> omega
theorem slK_range (j : Fin (7 + 1)) : RK x y (slK x y j).val := by
  have := j.isLt; show RK x y (mK x y j.val); unfold RK mK; split_ifs <;> omega
theorem slC1_range (j : Fin (3 + 1)) : RC1 x y (slC1 x y j).val := by
  have := j.isLt; show RC1 x y (mC1 x y j.val); unfold RC1 mC1; split_ifs <;> omega
theorem slR2_range (j : Fin (15 + 1)) : RR x y (slR2 x y j).val := by
  have := j.isLt; show RR x y (mR x y j.val); unfold RR mR; split_ifs <;> omega
theorem slC2_range (j : Fin (3 + 1)) : RC2 x y (slC2 x y j).val := by
  have := j.isLt; show RC2 x y (mC2 x y j.val); unfold RC2 mC2; split_ifs <;> omega
theorem slDd_range (j : Fin 3) : RD x y (slDd x y j).val := by
  have := j.isLt; show RD x y (mDd x y j.val); unfold RD mDd; split_ifs <;> omega
theorem slDn_range (j : Fin 3) : RD x y (slDn x y j).val := by
  have := j.isLt; show RD x y (mDn x y j.val); unfold RD mDn; split_ifs <;> omega

/-- A one-input entry bank under a masked reset, evaluated at a local port. -/
theorem addCases_single {k : ℕ} (hk : 0 < k) (src : List Bool) (f : Fin k → List Bool)
    (hf : ∀ j : Fin k, f j = if j.val = 0 then src else []) (j : Fin (k + 1)) :
    Fin.addCases (m := k) (n := 1) (motive := fun _ => List Bool) f (fun _ => []) j = if j.val = 0 then src else [] := by
  refine Fin.addCases (m := k) (n := 1) (fun i => ?_) (fun i => ?_) j
  · rw [Fin.addCases_left, hf]
    rfl
  · rw [Fin.addCases_right]
    have hv : (Fin.natAdd k i).val ≠ 0 := by simp only [Fin.val_natAdd]; omega
    rw [if_neg hv]

/-! ## 2. The machine -/

variable (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm)

abbrev xN := (nStage selector a).extra
abbrev yB := (bStage selector a).extra

def stDd := RecoveryFocus.machine (slDd (xN selector a) (yB selector a))
  (RepairSource.ProjectionNormalization.DimensionTemplate.machine false)
def stDn := RecoveryFocus.machine (slDn (xN selector a) (yB selector a))
  (RepairSource.ProjectionNormalization.DimensionTemplate.machine false)

/-- The `true` branch: read the degree, compare it with `N`, write the smaller one's template. -/
def branchT := Composition.machine (Composition.machine
  (RecoveryFocus.machine (slR2 (xN selector a) (yB selector a)) (MaskedReset.machine readChain (fun _ => true)))
  (RecoveryFocus.machine (slC2 (xN selector a) (yB selector a))
    (MaskedReset.machine MatrixBucketDimensions.Compare.raw (fun _ => true))))
  (CloseoutRowsOriginalSwitch.machine (stDd selector a) (stDn selector a) (flag2 (xN selector a) (yB selector a)))

/-- **Header 282's machine**. -/
def minMachine := Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine
    (RecoveryFocus.machine (slN (xN selector a) (yB selector a))
      (MaskedReset.machine (nStage selector a).machine (fun _ => true)))
    (RecoveryFocus.machine (slB (xN selector a) (yB selector a))
      (MaskedReset.machine (bStage selector a).machine (fun _ => true))))
    (RecoveryFocus.machine (slU2 (xN selector a) (yB selector a))
      (MaskedReset.machine GeneratedAmplifier.Copy.machine (fun _ => true))))
    (RecoveryFocus.machine (slK (xN selector a) (yB selector a)) (MaskedReset.machine skipChain (fun _ => true))))
    (RecoveryFocus.machine (slC1 (xN selector a) (yB selector a))
      (MaskedReset.machine MatrixBucketDimensions.Compare.raw (fun _ => true))))
  (CloseoutRowsOriginalSwitch.machine (branchT selector a) (stDn selector a) (flag1 (xN selector a) (yB selector a)))

/-- The prefix cost (before the switch) and the switch's common bound. -/
def preCost (r : Request) (w deg C : ℕ) (caps : RowCaps) : ℕ :=
  ((((2 * (nStage selector a).cost r + 2) + 1 + (2 * (bStage selector a).cost r + 2)) + 1 +
    (2 * (2 * (RowsInit.metaWord w deg C caps.headerFuel caps.copyCap caps.descriptorReserve
      caps.rawReserve).length + 1) + 2)) + 1 + (2 * skipCost w deg + 2)) + 1 +
    (2 * (min (natBitLength deg) (natBitLength (poolN selector a r)) + 2) + 2)
def swCost (w N : ℕ) : ℕ :=
  (2 * readCost w (2 * N + 1) + 2) + 1 + (2 * (N + 2) + 2) + 1 + ((2 * (2 * N + 1) + 8) + 2) + 2

/-! ## 3. The run -/

theorem readCost_mono (w : ℕ) {d1 d2 : ℕ} (h : d1 ≤ d2) : readCost w d1 ≤ readCost w d2 := by
  have hb : natBitLength d1 ≤ natBitLength d2 := by
    unfold natBitLength
    have := Nat.log_mono_right (b := 2) h
    omega
  unfold readCost
  omega

set_option maxHeartbeats 1000000 in
/-- **Header 282's run**: from the framed request, the metadata word and `tape N` to `tape (min degree N)` on local 3. -/
theorem min_run (r : Request) (w deg C : ℕ) (caps : RowCaps) :
    ∃ A' : Fin (4 + (33 + xN selector a + yB selector a)) → List Bool,
      Step (minMachine selector a) (preCost selector a r w deg C caps + 1 + swCost w (poolN selector a r)) (fun _ => 0)
        (h282In (33 + xN selector a + yB selector a) (frame (r.input a)) (rowMetadataWord w deg C caps)
          (UnaryTemplate.tape (poolN selector a r))) (fun _ => 0) A' ∧
      A' ⟨0, by omega⟩ = frame (r.input a) ∧ A' ⟨1, by omega⟩ = rowMetadataWord w deg C caps ∧
      A' ⟨2, by omega⟩ = UnaryTemplate.tape (poolN selector a r) ∧
      A' ⟨3, by omega⟩ = UnaryTemplate.tape (min deg (poolN selector a r)) := by
  classical
  have hxe : xN selector a = (nStage selector a).extra := rfl
  have hye : yB selector a = (bStage selector a).extra := rfl
  have hm := unwrap_meta w deg C caps
  set m := RowsInit.metaWord w deg C caps.headerFuel caps.copyCap caps.descriptorReserve caps.rawReserve with hmdef
  set rest := natWord C ++ natWord 4 ++ natWord caps.headerFuel ++ natWord caps.copyCap ++
    natWord caps.descriptorReserve ++ natWord caps.rawReserve with hrest
  set src := natWord 3 ++ natWord w ++ natWord deg ++ rest with hsrc
  have hms : m = src := by
    rw [hmdef, RowsInit.metaWord_eq, hsrc, hrest]
    simp only [List.append_assoc]
  set N := poolN selector a r with hN
  set A0 := h282In (33 + xN selector a + yB selector a) (frame (r.input a)) (rowMetadataWord w deg C caps)
    (UnaryTemplate.tape N) with hA0
  have a0b : ∀ z : Fin (4 + (33 + xN selector a + yB selector a)), 3 ≤ z.val → A0 z = [] := by
    intro z hz
    rw [hA0]
    unfold h282In
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have a0bv : ∀ v (hv : v < 4 + (33 + xN selector a + yB selector a)), 3 ≤ v → A0 ⟨v, hv⟩ = [] :=
    fun v hv h => a0b ⟨v, hv⟩ h
  -- 1. `1^N`
  obtain ⟨BN, rN, bN0, bN1⟩ := RowsInit.stage_masked (nStage selector a) r
  have dN := RowsInit.VecDock.run_dock rN (slN (xN selector a) (yB selector a)) (slN_inj _ _) (fun _ => 0) A0
    (fun _ => rfl) (fun j => by
      by_cases hj : j.val = 0
      · obtain ⟨jv, hjv⟩ := j
        simp only at hj
        subst hj
        rw [RowsInit.VecDock.vin_zero _ _ (by omega)]
        rfl
      · rw [RowsInit.VecDock.vin_blank _ _ j hj]
        have hv : (slN (xN selector a) (yB selector a) j).val = j.val + 3 := by
          show mN j.val = _
          unfold mN
          rw [if_neg hj]
        exact a0b _ (by omega))
  set A1 := install (slN (xN selector a) (yB selector a)) A0 BN with hA1
  have o1 : ∀ v (hv : v < 4 + (33 + xN selector a + yB selector a)), ¬ RN (xN selector a) v → A1 ⟨v, hv⟩ = A0 ⟨v, hv⟩ :=
    fun v hv h => install_other _ _ _ _ (not_hit _ _ (slN_range _ _) ⟨v, hv⟩ h)
  have a1_0 : A1 ⟨0, by omega⟩ = frame (r.input a) := (install_slot _ (slN_inj _ _) _ _ ⟨0, by omega⟩).trans bN0
  have a1_4 : A1 ⟨4, by omega⟩ = List.replicate N true := (install_slot _ (slN_inj _ _) _ _ ⟨1, by omega⟩).trans bN1
  -- 2. `1^(natBitLength N)`
  obtain ⟨BB, rB, bB0, bB1⟩ := RowsInit.stage_masked (bStage selector a) r
  have dB := RowsInit.VecDock.run_dock rB (slB (xN selector a) (yB selector a)) (slB_inj _ _) (fun _ => 0) A1
    (fun _ => rfl) (fun j => by
      by_cases hj : j.val = 0
      · obtain ⟨jv, hjv⟩ := j
        simp only at hj
        subst hj
        rw [RowsInit.VecDock.vin_zero _ _ (by omega)]
        exact a1_0
      · rw [RowsInit.VecDock.vin_blank _ _ j hj]
        have hlt := j.isLt
        have hv : 6 + xN selector a ≤ (slB (xN selector a) (yB selector a) j).val ∧
            (slB (xN selector a) (yB selector a) j).val ≤ 7 + xN selector a + yB selector a := by
          show 6 + xN selector a ≤ mB _ j.val ∧ mB _ j.val ≤ _
          unfold mB
          split_ifs <;> omega
        refine (install_other _ _ _ _ (not_hit _ _ (slN_range _ _) _ (by unfold RN; omega))).trans ?_
        exact a0b _ (by omega))
  set A2 := install (slB (xN selector a) (yB selector a)) A1 BB with hA2
  have o2 : ∀ v (hv : v < 4 + (33 + xN selector a + yB selector a)), ¬ RB (xN selector a) (yB selector a) v →
      A2 ⟨v, hv⟩ = A1 ⟨v, hv⟩ :=
    fun v hv h => install_other _ _ _ _ (not_hit _ _ (slB_range _ _) ⟨v, hv⟩ h)
  have a2_0 : A2 ⟨0, by omega⟩ = frame (r.input a) := (install_slot _ (slB_inj _ _) _ _ ⟨0, by omega⟩).trans bB0
  have a2_b : A2 ⟨6 + xN selector a, by omega⟩ = List.replicate (natBitLength N) true :=
    (install_slot _ (slB_inj _ _) _ _ ⟨1, by omega⟩).trans bB1
  have blank2 : ∀ v (hv : v < 4 + (33 + xN selector a + yB selector a)), 8 + xN selector a + yB selector a ≤ v →
      A2 ⟨v, hv⟩ = [] := fun v hv h =>
    (o2 v hv (by unfold RB; omega)).trans ((o1 v hv (by unfold RN; omega)).trans (a0bv v hv (by omega)))
  -- 3. unwrap the metadata word
  obtain ⟨BU, rU, bU0, bU1⟩ := unwrap_run m
  have dU := RowsInit.VecDock.run_dock rU (slU2 (xN selector a) (yB selector a)) (slU2_inj _ _) (fun _ => 0) A2
    (fun _ => rfl) (fun j => by
      fin_cases j
      · exact ((o2 1 (by omega) (by unfold RB; omega)).trans (o1 1 (by omega) (by unfold RN; omega))).trans hm
      · exact blank2 (8 + xN selector a + yB selector a) (by omega) (by omega)
      · exact blank2 (9 + xN selector a + yB selector a) (by omega) (by omega))
  set A3 := install (slU2 (xN selector a) (yB selector a)) A2 BU with hA3
  have o3 : ∀ v (hv : v < 4 + (33 + xN selector a + yB selector a)), ¬ RU2 (xN selector a) (yB selector a) v →
      A3 ⟨v, hv⟩ = A2 ⟨v, hv⟩ :=
    fun v hv h => install_other _ _ _ _ (not_hit _ _ (slU2_range _ _) ⟨v, hv⟩ h)
  have a3_1 : A3 ⟨1, by omega⟩ = frame m := (install_slot _ (slU2_inj _ _) _ _ 0).trans bU0
  have a3_u : A3 ⟨8 + xN selector a + yB selector a, by omega⟩ = m :=
    (install_slot _ (slU2_inj _ _) _ _ 1).trans bU1
  have blank3 : ∀ v (hv : v < 4 + (33 + xN selector a + yB selector a)), 10 + xN selector a + yB selector a ≤ v →
      A3 ⟨v, hv⟩ = [] := fun v hv h =>
    (o3 v hv (by unfold RU2; omega)).trans (blank2 v hv (by omega))
  -- 4. the skip pass
  obtain ⟨BK, rK, bK0, bK5⟩ := skip_masked w deg rest
  have dK := RowsInit.VecDock.run_dock rK (slK (xN selector a) (yB selector a)) (slK_inj _ _) (fun _ => 0) A3
    (fun _ => rfl) (fun j => by
      rw [addCases_single (by omega) src (kIn src) (fun _ => rfl) j]
      by_cases hj : j.val = 0
      · rw [if_pos hj]
        obtain ⟨jv, hjv⟩ := j
        simp only at hj
        subst hj
        exact a3_u.trans hms
      · rw [if_neg hj]
        have hlt := j.isLt
        have hv : 10 + xN selector a + yB selector a ≤ mK (xN selector a) (yB selector a) j.val := by
          unfold mK
          split_ifs <;> omega
        exact blank3 (mK (xN selector a) (yB selector a) j.val) (slK _ _ j).isLt hv)
  set A4 := install (slK (xN selector a) (yB selector a)) A3 BK with hA4
  have o4 : ∀ v (hv : v < 4 + (33 + xN selector a + yB selector a)), ¬ RK (xN selector a) (yB selector a) v →
      A4 ⟨v, hv⟩ = A3 ⟨v, hv⟩ :=
    fun v hv h => install_other _ _ _ _ (not_hit _ _ (slK_range _ _) ⟨v, hv⟩ h)
  have a4_u : A4 ⟨8 + xN selector a + yB selector a, by omega⟩ = src := (install_slot _ (slK_inj _ _) _ _ 0).trans bK0
  have a4_t : A4 ⟨14 + xN selector a + yB selector a, by omega⟩ = UnaryTemplate.tape (natBitLength deg) :=
    (install_slot _ (slK_inj _ _) _ _ 5).trans bK5
  have blank4 : ∀ v (hv : v < 4 + (33 + xN selector a + yB selector a)), 17 + xN selector a + yB selector a ≤ v →
      A4 ⟨v, hv⟩ = [] := fun v hv h =>
    (o4 v hv (by unfold RK; omega)).trans (blank3 v hv (by omega))
  -- 5. compare the bit lengths
  obtain ⟨BC, rC, bC0, bC1, bC2⟩ := cmp_masked (natBitLength deg) (natBitLength N)
  have dC := RowsInit.VecDock.run_dock rC (slC1 (xN selector a) (yB selector a)) (slC1_inj _ _) (fun _ => 0) A4
    (fun _ => rfl) (fun j => by
      fin_cases j
      · exact a4_t
      · exact (o4 (6 + xN selector a) (by omega) (by unfold RK; omega)).trans
          ((o3 (6 + xN selector a) (by omega) (by unfold RU2; omega)).trans a2_b)
      · exact blank4 (17 + xN selector a + yB selector a) (by omega) (by omega)
      · exact blank4 (18 + xN selector a + yB selector a) (by omega) (by omega))
  set A5 := install (slC1 (xN selector a) (yB selector a)) A4 BC with hA5
  have o5 : ∀ v (hv : v < 4 + (33 + xN selector a + yB selector a)), ¬ RC1 (xN selector a) (yB selector a) v →
      A5 ⟨v, hv⟩ = A4 ⟨v, hv⟩ :=
    fun v hv h => install_other _ _ _ _ (not_hit _ _ (slC1_range _ _) ⟨v, hv⟩ h)
  have a5_f : A5 (flag1 (xN selector a) (yB selector a)) = [decide (natBitLength deg ≤ natBitLength N)] :=
    (install_slot _ (slC1_inj _ _) _ _ 2).trans bC2
  have a5_0 : A5 ⟨0, by omega⟩ = frame (r.input a) :=
    (o5 0 _ (by unfold RC1; omega)).trans ((o4 0 _ (by unfold RK; omega)).trans ((o3 0 _ (by unfold RU2; omega)).trans a2_0))
  have a5_1 : A5 ⟨1, by omega⟩ = rowMetadataWord w deg C caps :=
    (o5 1 _ (by unfold RC1; omega)).trans ((o4 1 _ (by unfold RK; omega)).trans (a3_1.trans hm.symm))
  have a5_2 : A5 ⟨2, by omega⟩ = UnaryTemplate.tape N :=
    (o5 2 _ (by unfold RC1; omega)).trans ((o4 2 _ (by unfold RK; omega)).trans ((o3 2 _ (by unfold RU2; omega)).trans
      ((o2 2 _ (by unfold RB; omega)).trans ((o1 2 _ (by unfold RN; omega)).trans rfl))))
  have a5_3 : A5 ⟨3, by omega⟩ = [] :=
    (o5 3 _ (by unfold RC1; omega)).trans ((o4 3 _ (by unfold RK; omega)).trans ((o3 3 _ (by unfold RU2; omega)).trans
      ((o2 3 _ (by unfold RB; omega)).trans ((o1 3 _ (by unfold RN; omega)).trans (a0bv 3 _ (by omega))))))
  have a5_4 : A5 ⟨4, by omega⟩ = List.replicate N true :=
    (o5 4 _ (by unfold RC1; omega)).trans ((o4 4 _ (by unfold RK; omega)).trans ((o3 4 _ (by unfold RU2; omega)).trans
      ((o2 4 _ (by unfold RB; omega)).trans a1_4)))
  have a5_u : A5 ⟨8 + xN selector a + yB selector a, by omega⟩ = src := (o5 _ _ (by unfold RC1; omega)).trans a4_u
  have blank5 : ∀ v (hv : v < 4 + (33 + xN selector a + yB selector a)), 19 + xN selector a + yB selector a ≤ v →
      A5 ⟨v, hv⟩ = [] := fun v hv h =>
    (o5 v hv (by unfold RC1; omega)).trans (blank4 v hv (by omega))
  have pre := (((dN.seq dB).seq dU).seq dK).seq dC
  -- 6. the switch
  have hD : ∀ (A7 : Fin (4 + (33 + xN selector a + yB selector a)) → List Bool) (n : ℕ)
      (sl : Fin 3 → Fin (4 + (33 + xN selector a + yB selector a))) (hsl : Function.Injective sl)
      (hR : ∀ j, RD (xN selector a) (yB selector a) (sl j).val) (h1 : sl 1 = ⟨3, by omega⟩)
      (hin : A7 (sl 0) = List.replicate n true) (h3 : A7 ⟨3, by omega⟩ = [])
      (hT : A7 (sl 2) = []),
      Step (RecoveryFocus.machine sl (RepairSource.ProjectionNormalization.DimensionTemplate.machine false)) (2 * n + 8)
        (fun _ => 0) A7 (fun _ => 0) (install sl A7 ![List.replicate n true, UnaryTemplate.tape n, List.replicate (n + 3) false]) ∧
      (∀ v (hv : v < 4 + (33 + xN selector a + yB selector a)), ¬ RD (xN selector a) (yB selector a) v →
        install sl A7 ![List.replicate n true, UnaryTemplate.tape n, List.replicate (n + 3) false] ⟨v, hv⟩ = A7 ⟨v, hv⟩) ∧
      install sl A7 ![List.replicate n true, UnaryTemplate.tape n, List.replicate (n + 3) false] ⟨3, by omega⟩ =
        UnaryTemplate.tape n := by
    intro A7 n sl hsl hR h1 hin h3 hT
    refine ⟨RowsInit.VecDock.run_dock (dt_run n) sl hsl (fun _ => 0) A7 (fun _ => rfl) (fun j => by
      fin_cases j
      · exact hin
      · exact (congrArg A7 h1).trans h3
      · exact hT), fun v hv h => install_other _ _ _ _ (not_hit _ _ hR ⟨v, hv⟩ h), ?_⟩
    rw [← h1]
    exact install_slot _ hsl _ _ 1
  have key : ∃ Af : Fin (4 + (33 + xN selector a + yB selector a)) → List Bool,
      Step (CloseoutRowsOriginalSwitch.machine (branchT selector a) (stDn selector a) (flag1 (xN selector a) (yB selector a)))
        (swCost w N) (fun _ => 0) A5 (fun _ => 0) Af ∧
      Af ⟨0, by omega⟩ = frame (r.input a) ∧ Af ⟨1, by omega⟩ = rowMetadataWord w deg C caps ∧
      Af ⟨2, by omega⟩ = UnaryTemplate.tape N ∧ Af ⟨3, by omega⟩ = UnaryTemplate.tape (min deg N) := by
    by_cases hbb : natBitLength deg ≤ natBitLength N
    · have hdeg := bits_true deg N hbb
      -- read the degree
      obtain ⟨BR, rR, bR0, bR12, bR14⟩ := read_masked w deg rest
      have dR := RowsInit.VecDock.run_dock rR (slR2 (xN selector a) (yB selector a)) (slR2_inj _ _) (fun _ => 0) A5
        (fun _ => rfl) (fun j => by
          rw [addCases_single (by omega) src (rIn src) (fun _ => rfl) j]
          by_cases hj : j.val = 0
          · rw [if_pos hj]
            obtain ⟨jv, hjv⟩ := j
            simp only at hj
            subst hj
            exact a5_u
          · rw [if_neg hj]
            have hlt := j.isLt
            have hv : 19 + xN selector a + yB selector a ≤ mR (xN selector a) (yB selector a) j.val := by
              unfold mR
              split_ifs <;> omega
            exact blank5 (mR (xN selector a) (yB selector a) j.val) (slR2 _ _ j).isLt hv)
      set A6 := install (slR2 (xN selector a) (yB selector a)) A5 BR with hA6
      have o6 : ∀ v (hv : v < 4 + (33 + xN selector a + yB selector a)), ¬ RR (xN selector a) (yB selector a) v →
          A6 ⟨v, hv⟩ = A5 ⟨v, hv⟩ :=
        fun v hv h => install_other _ _ _ _ (not_hit _ _ (slR2_range _ _) ⟨v, hv⟩ h)
      have a6_d : A6 ⟨30 + xN selector a + yB selector a, by omega⟩ = List.replicate deg true :=
        (install_slot _ (slR2_inj _ _) _ _ 12).trans bR12
      have a6_t : A6 ⟨32 + xN selector a + yB selector a, by omega⟩ = UnaryTemplate.tape deg :=
        (install_slot _ (slR2_inj _ _) _ _ 14).trans bR14
      -- compare the degree with `N`
      obtain ⟨BC2, rC2, c20, c21, c22⟩ := cmp_masked deg N
      have dC2 := RowsInit.VecDock.run_dock rC2 (slC2 (xN selector a) (yB selector a)) (slC2_inj _ _) (fun _ => 0) A6
        (fun _ => rfl) (fun j => by
          fin_cases j
          · exact a6_t
          · exact (o6 4 _ (by unfold RR; omega)).trans a5_4
          · exact (o6 (34 + xN selector a + yB selector a) (by omega) (by unfold RR; omega)).trans
              (blank5 (34 + xN selector a + yB selector a) (by omega) (by omega))
          · exact (o6 (35 + xN selector a + yB selector a) (by omega) (by unfold RR; omega)).trans
              (blank5 (35 + xN selector a + yB selector a) (by omega) (by omega)))
      set A7 := install (slC2 (xN selector a) (yB selector a)) A6 BC2 with hA7
      have o7 : ∀ v (hv : v < 4 + (33 + xN selector a + yB selector a)), ¬ RC2 (xN selector a) (yB selector a) v →
          A7 ⟨v, hv⟩ = A6 ⟨v, hv⟩ :=
        fun v hv h => install_other _ _ _ _ (not_hit _ _ (slC2_range _ _) ⟨v, hv⟩ h)
      have a7_f : A7 (flag2 (xN selector a) (yB selector a)) = [decide (deg ≤ N)] :=
        (install_slot _ (slC2_inj _ _) _ _ 2).trans c22
      have a7_4 : A7 ⟨4, by omega⟩ = List.replicate N true := (install_slot _ (slC2_inj _ _) _ _ 1).trans c21
      have a7_d : A7 ⟨30 + xN selector a + yB selector a, by omega⟩ = List.replicate deg true :=
        (o7 _ _ (by unfold RC2; omega)).trans a6_d
      have a7_3 : A7 ⟨3, by omega⟩ = [] :=
        (o7 3 _ (by unfold RC2; omega)).trans ((o6 3 _ (by unfold RR; omega)).trans a5_3)
      have a7_T : A7 ⟨36 + xN selector a + yB selector a, by omega⟩ = [] :=
        (o7 _ _ (by unfold RC2; omega)).trans ((o6 _ _ (by unfold RR; omega)).trans (blank5 _ _ (by omega)))
      have keep7 : ∀ v (hv : v < 4 + (33 + xN selector a + yB selector a)), v ≤ 2 → A7 ⟨v, hv⟩ = A5 ⟨v, hv⟩ :=
        fun v hv h => (o7 v hv (by unfold RC2; omega)).trans (o6 v hv (by unfold RR; omega))
      have hb1 : readTapeBit (A5 (flag1 (xN selector a) (yB selector a)))
          ((fun _ => 0) (flag1 (xN selector a) (yB selector a))) = true := by
        rw [a5_f]
        exact decide_eq_true hbb
      by_cases hdn : deg ≤ N
      · obtain ⟨dD, oD, aD⟩ := hD A7 deg (slDd (xN selector a) (yB selector a)) (slDd_inj _ _) (slDd_range _ _) rfl
          a7_d a7_3 a7_T
        have hb2 : readTapeBit (A7 (flag2 (xN selector a) (yB selector a)))
            ((fun _ => 0) (flag2 (xN selector a) (yB selector a))) = true := by
          rw [a7_f]
          exact decide_eq_true hdn
        have sw2 := CloseoutRowsOriginalSwitch.true_run (stDd selector a) (stDn selector a)
          (flag2 (xN selector a) (yB selector a)) dD hb2
        have sw1 := CloseoutRowsOriginalSwitch.true_run (branchT selector a) (stDn selector a)
          (flag1 (xN selector a) (yB selector a)) ((dR.seq dC2).seq sw2) hb1
        refine ⟨_, sw1.enlarge ?_, ?_, ?_, ?_, ?_⟩
        · have := readCost_mono w (show deg ≤ 2 * N + 1 by omega)
          have := min_le_right deg N
          unfold swCost
          omega
        · exact (oD 0 _ (by unfold RD; omega)).trans ((keep7 0 _ (by omega)).trans a5_0)
        · exact (oD 1 _ (by unfold RD; omega)).trans ((keep7 1 _ (by omega)).trans a5_1)
        · exact (oD 2 _ (by unfold RD; omega)).trans ((keep7 2 _ (by omega)).trans a5_2)
        · rw [min_eq_left hdn]
          exact aD
      · obtain ⟨dD, oD, aD⟩ := hD A7 N (slDn (xN selector a) (yB selector a)) (slDn_inj _ _) (slDn_range _ _) rfl
          a7_4 a7_3 a7_T
        have hb2 : readTapeBit (A7 (flag2 (xN selector a) (yB selector a)))
            ((fun _ => 0) (flag2 (xN selector a) (yB selector a))) = false := by
          rw [a7_f]
          exact decide_eq_false hdn
        have sw2 := CloseoutRowsOriginalSwitch.false_run (stDd selector a) (stDn selector a)
          (flag2 (xN selector a) (yB selector a)) dD hb2
        have sw1 := CloseoutRowsOriginalSwitch.true_run (branchT selector a) (stDn selector a)
          (flag1 (xN selector a) (yB selector a)) ((dR.seq dC2).seq sw2) hb1
        refine ⟨_, sw1.enlarge ?_, ?_, ?_, ?_, ?_⟩
        · have := readCost_mono w hdeg
          have := min_le_right deg N
          unfold swCost
          omega
        · exact (oD 0 _ (by unfold RD; omega)).trans ((keep7 0 _ (by omega)).trans a5_0)
        · exact (oD 1 _ (by unfold RD; omega)).trans ((keep7 1 _ (by omega)).trans a5_1)
        · exact (oD 2 _ (by unfold RD; omega)).trans ((keep7 2 _ (by omega)).trans a5_2)
        · rw [min_eq_right (by omega)]
          exact aD
    · have hlt := bits_false deg N (by omega)
      obtain ⟨dD, oD, aD⟩ := hD A5 N (slDn (xN selector a) (yB selector a)) (slDn_inj _ _) (slDn_range _ _) rfl
        a5_4 a5_3 (blank5 (36 + xN selector a + yB selector a) (by omega) (by omega))
      have hb1 : readTapeBit (A5 (flag1 (xN selector a) (yB selector a)))
          ((fun _ => 0) (flag1 (xN selector a) (yB selector a))) = false := by
        rw [a5_f]
        exact decide_eq_false hbb
      have sw1 := CloseoutRowsOriginalSwitch.false_run (branchT selector a) (stDn selector a)
        (flag1 (xN selector a) (yB selector a)) dD hb1
      refine ⟨_, sw1.enlarge ?_, ?_, ?_, ?_, ?_⟩
      · unfold swCost
        omega
      · exact (oD 0 _ (by unfold RD; omega)).trans a5_0
      · exact (oD 1 _ (by unfold RD; omega)).trans a5_1
      · exact (oD 2 _ (by unfold RD; omega)).trans a5_2
      · rw [min_eq_right (by omega)]
        exact aD
  obtain ⟨Af, hsw, f0, f1, f2, f3⟩ := key
  exact ⟨Af, pre.seq hsw, f0, f1, f2, f3⟩

/-! ## 4. The cost and the `H282Spec` term -/

def minCoef : ℕ := 300 * ((nStage selector a).coefficient + (bStage selector a).coefficient + 8)
def minDeg : ℕ := max (bStage selector a).degree ((nStage selector a).degree + 1)

/-- **The stage sum fits** `coefficient·(smallSize^degree + |meta| + 1)`, for every request and metadata. -/
theorem min_cost_le (r : Request) (w deg C : ℕ) (caps : RowCaps) :
    preCost selector a r w deg C caps + 1 + swCost w (poolN selector a r) ≤
      minCoef selector a * ((r.smallSize a) ^ minDeg selector a + (rowMetadataWord w deg C caps).length + 1) := by
  have hS := RowsInit.small_pos a r
  have p1 : (r.smallSize a) ^ (nStage selector a).degree ≤ (r.smallSize a) ^ minDeg selector a :=
    Nat.pow_le_pow_right hS (by unfold minDeg; omega)
  have p2 : (r.smallSize a) ^ ((nStage selector a).degree + 1) ≤ (r.smallSize a) ^ minDeg selector a :=
    Nat.pow_le_pow_right hS (by unfold minDeg; omega)
  have p3 : (r.smallSize a) ^ (bStage selector a).degree ≤ (r.smallSize a) ^ minDeg selector a :=
    Nat.pow_le_pow_right hS (by unfold minDeg; omega)
  have c1 := (nStage selector a).cost_le r
  have c2 := (bStage selector a).cost_le r
  have vb := (nStage selector a).value_bound r
  have hmeta : (rowMetadataWord w deg C caps).length = 2 * (RowsInit.metaWord w deg C caps.headerFuel caps.copyCap
      caps.descriptorReserve caps.rawReserve).length + 1 := by
    rw [unwrap_meta, frame_length]
  have hml := congrArg List.length (RowsInit.metaWord_eq w deg C caps.headerFuel caps.copyCap caps.descriptorReserve
    caps.rawReserve)
  simp only [List.length_append, RowsInit.natWord_length] at hml
  have hb1 := RowsInit.bits_le (2 * poolN selector a r + 1)
  have hb2 := RowsInit.bits_le (poolN selector a r)
  have hmin := min_le_right (natBitLength deg) (natBitLength (poolN selector a r))
  set X := (r.smallSize a) ^ minDeg selector a + (rowMetadataWord w deg C caps).length + 1 with hX
  have q1 : (nStage selector a).coefficient * (r.smallSize a) ^ (nStage selector a).degree ≤
      (nStage selector a).coefficient * X := Nat.mul_le_mul_left _ (by omega)
  have q2 : (bStage selector a).coefficient * (r.smallSize a) ^ (bStage selector a).degree ≤
      (bStage selector a).coefficient * X := Nat.mul_le_mul_left _ (by omega)
  have q3 : ((nStage selector a).coefficient + 7) * (r.smallSize a) ^ ((nStage selector a).degree + 1) ≤
      (nStage selector a).coefficient * X + 7 * X := by
    calc ((nStage selector a).coefficient + 7) * (r.smallSize a) ^ ((nStage selector a).degree + 1)
        ≤ ((nStage selector a).coefficient + 7) * X := Nat.mul_le_mul_left _ (by omega)
      _ = (nStage selector a).coefficient * X + 7 * X := by ring
  have expand : minCoef selector a * X =
      300 * ((nStage selector a).coefficient * X) + 300 * ((bStage selector a).coefficient * X) + 2400 * X := by
    unfold minCoef
    ring
  rw [expand]
  unfold preCost swCost readCost skipCost
  omega

/-- **Header 282's producer**: ONE fixed machine (from `selector`, `a`), `cost_le` by definition. -/
def h282 : H282Spec selector a where
  extra := 33 + xN selector a + yB selector a
  states := _
  machine := minMachine selector a
  cost := fun r w deg C caps =>
    minCoef selector a * ((r.smallSize a) ^ minDeg selector a + (rowMetadataWord w deg C caps).length + 1)
  coefficient := minCoef selector a
  degree := minDeg selector a
  cost_le := fun _ _ _ _ _ => le_refl _
  run := fun r w deg C caps => by
    obtain ⟨A', h, h0, h1, h2, h3⟩ := min_run selector a r w deg C caps
    exact ⟨A', h.enlarge (min_cost_le selector a r w deg C caps), h0, h1, h2, h3⟩

end
end RowsHeaderW

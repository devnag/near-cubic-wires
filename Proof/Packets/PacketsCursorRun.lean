import Proof.Packets.PacketsCursorStage

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

section Runs
variable {base : Request → ℕ} (V : KeyVec a 9 (cursorOuts a base)) (cE kE : ℕ)

/-! ## 1. The nine words, masked -/

theorem run1 (r : Request) (k : rcKey a r) (hk : k ∈ rcKeys a r) (E : ℕ) :
    ∃ A1 : Fin (TS V.extra kE) → List Bool,
      Step (st1 V kE) (2 * V.cost r + 2) (fun _ => 0) (sEntry a V.extra kE r k E) (fun _ => 0) A1 ∧
      (∀ i : Fin (TS V.extra kE), i.val < 9 → A1 i = PacketsCombine.metaEntry a r (some k) (TS V.extra kE) i) ∧
      (∀ i : Fin (TS V.extra kE), 9 ≤ i.val → i.val < 18 → A1 i = cursorOuts a base (i.val - 9) r k) ∧
      A1 (tL V.extra kE) = List.replicate (E + 1) false ∧
      (∀ i : Fin (TS V.extra kE), iD V.extra ≤ i.val → A1 i = []) ∧
      (∀ i : Fin (TS V.extra kE), 9 ≤ i.val → i.val ≠ iL V.extra → (A1 i).length ≤ 2 * V.cost r + 3) := by
  obtain ⟨H, A, st, keep, outs⟩ := V.run r k hk
  obtain ⟨kk, sm⟩ := step_mask0 st (fun _ => true) (fun _ _ => rfl)
  have hin : ∀ j : Fin (9 + 9 + V.extra + 1),
      (fun _ => 0) (ι1 V.extra kE j) = Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun _ : Fin 1 => 0) j ∧
      sEntry a V.extra kE r k E (ι1 V.extra kE j) = ZeroPadding.pad 0
        (Fin.addCases (motive := fun _ => List Bool) (PacketsCombine.metaEntry a r (some k) (9 + 9 + V.extra))
          (fun _ : Fin 1 => ([] : List Bool)) j) := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · refine ⟨by simp, ?_⟩
      simp only [Fin.addCases_left, ZeroPadding.pad_zero]
      unfold sEntry
      have hv : (ι1 V.extra kE (Fin.castAdd 1 i)).val = i.val := rfl
      by_cases h9 : i.val < 9
      · rw [if_pos (by rw [hv]; exact h9)]
        exact me_congr r (some k) _ _ hv
      · have hi := i.isLt
        rw [if_neg (by rw [hv]; exact h9), if_neg (by rw [hv]; unfold iL; omega), me_hi r (some k) _ (by omega)]
    · refine ⟨by simp, ?_⟩
      simp only [Fin.addCases_right, ZeroPadding.pad_zero]
      unfold sEntry
      have hv : (ι1 V.extra kE (Fin.natAdd (9 + 9 + V.extra) i)).val = 9 + 9 + V.extra + i.val := rfl
      have hi := i.isLt
      rw [if_neg (by rw [hv]; omega), if_neg (by rw [hv]; unfold iL; omega)]
  obtain ⟨H1, A1, s1, hs, ho⟩ := Dock.lift sm (ι1 V.extra kE) (ι1_inj _ _) (fun _ => 0) (fun _ => 0)
    (sEntry a V.extra kE r k E) hin
  have hnot : ∀ i : Fin (TS V.extra kE), iL V.extra ≤ i.val → ∀ j, ι1 V.extra kE j ≠ i := by
    intro i hi j h
    have hv : (ι1 V.extra kE j).val = i.val := congrArg Fin.val h
    have := j.isLt
    change j.val = i.val at hv
    unfold iL at hi
    omega
  have hH : H1 = fun _ => 0 := by
    funext i
    by_cases hi : i.val < iL V.extra
    · have e : i = ι1 V.extra kE ⟨i.val, by unfold iL at hi; omega⟩ := Fin.ext rfl
      rw [e, (hs _).1]
      refine Fin.addCases (motive := fun j => Fin.addCases (motive := fun _ => ℕ)
        (fun i => if (fun _ => true) i = true then 0 else H i) (fun _ : Fin 1 => 0) j = 0)
        (fun i => ?_) (fun i => ?_) ⟨i.val, by unfold iL at hi; omega⟩
      · simp
      · simp
    · exact (ho i (hnot i (by omega))).1
  refine ⟨A1, s1.congr hH rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have e : i = ι1 V.extra kE (Fin.castAdd 1 ⟨i.val, by omega⟩) := Fin.ext rfl
    rw [e, (hs _).2, Fin.addCases_left, ZeroPadding.pad_zero, (keep _ hi).1]
    exact me_congr r (some k) _ _ rfl
  · intro i h9 h18
    have e : ι1 V.extra kE (Fin.castAdd 1 ⟨9 + (i.val - 9), by omega⟩) = i := Fin.ext (by
      change 9 + (i.val - 9) = i.val; omega)
    have h := (hs (Fin.castAdd 1 ⟨9 + (i.val - 9), by omega⟩)).2
    rw [Fin.addCases_left, ZeroPadding.pad_zero, (outs (i.val - 9) (by omega)).1, e] at h
    exact h
  · have := ho (tL V.extra kE) (hnot _ le_rfl)
    rw [this.2]
    unfold sEntry
    rw [if_neg (by rw [tL_val]; unfold iL; omega), if_pos (tL_val _ _)]
  · intro i hi
    have hi' : iL V.extra ≤ i.val := by unfold iD at hi; unfold iL; omega
    rw [(ho i (hnot i hi')).2]
    unfold sEntry
    rw [if_neg (by unfold iD at hi; omega), if_neg (by unfold iD at hi; unfold iL; omega)]
  · intro i h9 hL
    refine P1Closure.LocalSupport.step_fits s1 i (2 * V.cost r + 3) ?_ (by simp)
    unfold sEntry
    rw [if_neg (by omega), if_neg hL]
    simp

/-! ## 2. The erase driver -/

theorem run2 (r : Request) (k : rcKey a r) (A1 : Fin (TS V.extra kE) → List Bool)
    (hK : ∀ i : Fin (TS V.extra kE), 9 ≤ i.val → i.val < 18 → A1 i = cursorOuts a base (i.val - 9) r k)
    (hL : A1 (tL V.extra kE) = List.replicate (Ev cE kE base r + 1) false)
    (hD : ∀ i : Fin (TS V.extra kE), iD V.extra ≤ i.val → A1 i = []) :
    ∃ A2 : Fin (TS V.extra kE) → List Bool,
      Step (st2 V cE kE) (PacketsGlue.DriverPhase.cost cE kE (base r + 1)) (fun _ => 0) A1 (fun _ => 0) A2 ∧
      ∀ i : Fin (TS V.extra kE), A2 i =
        if i.val = iL V.extra then List.replicate (Ev cE kE base r + 1) false
        else if i.val = iD V.extra then List.replicate (Ev cE kE base r) true
        else if i.val = 17 then List.replicate (base r + 1) true
        else if iD V.extra < i.val then CompareMachine.word (base r + 1) else A1 i := by
  have hrun := PacketsGlue.DriverPhase.run cE kE (base r + 1)
  obtain ⟨H2, A2, s2, hs, ho⟩ := Dock.lift hrun (δ V.extra kE) (δ_inj _ _) (fun _ => 0) (fun _ => 0) A1 (by
    intro j
    refine ⟨rfl, ?_⟩
    rw [ZeroPadding.pad_zero]
    unfold PacketsGlue.DriverPhase.entryA
    have hv := δ_val V.extra kE j
    unfold δv at hv
    by_cases h0 : j.val = 0
    · rw [if_pos h0]
      rw [if_pos h0] at hv
      have e : δ V.extra kE j = tL V.extra kE := Fin.ext hv
      rw [e, hL]
      rfl
    · rw [if_neg h0]
      rw [if_neg h0] at hv
      by_cases h1 : j.val = 1
      · rw [if_pos h1] at hv
        rw [if_neg (by omega), hD _ (by rw [hv])]
      · rw [if_neg h1] at hv
        by_cases h2 : j.val = 2
        · rw [if_pos h2] at hv
          rw [if_pos h2, hK _ (by rw [hv]; omega) (by rw [hv]; omega), hv]
          exact cursorOuts_src base r k
        · rw [if_neg h2] at hv
          rw [if_neg h2, hD _ (by rw [hv]; unfold iD; omega)])
  have hH : H2 = fun _ => 0 := by
    funext i
    by_cases hi : ∃ j, δ V.extra kE j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (hs j).1
    · simp only [not_exists] at hi
      exact (ho i hi).1
  refine ⟨A2, s2.congr hH rfl, fun i => ?_⟩
  by_cases hiL : i.val = iL V.extra
  · have e : i = δ V.extra kE ⟨0, by omega⟩ := Fin.ext (by rw [δ_val]; unfold δv; simp [hiL])
    rw [e, (hs _).2, ZeroPadding.pad_zero, if_pos (by rw [← e]; exact hiL)]
    rfl
  · rw [if_neg hiL]
    by_cases hiD : i.val = iD V.extra
    · have e : i = δ V.extra kE ⟨1, by omega⟩ := Fin.ext (by rw [δ_val]; unfold δv; simp [hiD])
      rw [e, (hs _).2, ZeroPadding.pad_zero, if_pos (by rw [← e]; exact hiD)]
      rfl
    · rw [if_neg hiD]
      by_cases h17 : i.val = 17
      · have e : i = δ V.extra kE ⟨2, by omega⟩ := Fin.ext (by rw [δ_val]; unfold δv; simp [h17])
        rw [e, (hs _).2, ZeroPadding.pad_zero, if_pos (by rw [← e]; exact h17)]
        rfl
      · rw [if_neg h17]
        by_cases hgt : iD V.extra < i.val
        · have hlt := i.isLt
          unfold iD at hgt
          have e : i = δ V.extra kE ⟨i.val - (9 + 9 + V.extra), by unfold TS at hlt; omega⟩ := Fin.ext (by
            change i.val = δv V.extra (i.val - (9 + 9 + V.extra))
            unfold δv
            rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
            omega)
          rw [if_pos (by unfold iD; omega)]
          rw [e, (hs _).2, ZeroPadding.pad_zero]
          unfold PacketsGlue.DriverPhase.exitA
          simp only [show ¬ (i.val - (9 + 9 + V.extra) = 0) by omega, show ¬ (i.val - (9 + 9 + V.extra) = 1) by omega,
            show ¬ (i.val - (9 + 9 + V.extra) = 2) by omega, if_false]
        · rw [if_neg hgt]
          refine (ho i (fun j hj => ?_)).2
          have hv := congrArg Fin.val hj
          rw [δ_val] at hv
          unfold δv at hv
          unfold iL at hiL hv
          unfold iD at hiD hgt hv
          split_ifs at hv <;> omega

/-! ## 3. Erase what the first two phases wrote -/

theorem run3 (r : Request) (k : rcKey a r) (A1 A2 : Fin (TS V.extra kE) → List Bool)
    (h9 : ∀ i : Fin (TS V.extra kE), i.val < 9 → A1 i = PacketsCombine.metaEntry a r (some k) (TS V.extra kE) i)
    (hK : ∀ i : Fin (TS V.extra kE), 9 ≤ i.val → i.val < 18 → A1 i = cursorOuts a base (i.val - 9) r k)
    (hlen : ∀ i : Fin (TS V.extra kE), 9 ≤ i.val → i.val ≠ iL V.extra → (A1 i).length ≤ 2 * V.cost r + 3)
    (hA2 : ∀ i : Fin (TS V.extra kE), A2 i =
        if i.val = iL V.extra then List.replicate (Ev cE kE base r + 1) false
        else if i.val = iD V.extra then List.replicate (Ev cE kE base r) true
        else if i.val = 17 then List.replicate (base r + 1) true
        else if iD V.extra < i.val then CompareMachine.word (base r + 1) else A1 i)
    (hE1 : base r + 2 ≤ Ev cE kE base r) (hE2 : 2 * V.cost r + 3 ≤ Ev cE kE base r) :
    Step (st3 V kE) (2 * Ev cE kE base r + 4) (fun _ => 0) A2 (fun _ => 0)
      (s3 a base V.extra kE r k (Ev cE kE base r)) := by
  have hne : tD V.extra kE ≠ tL V.extra kE := by
    intro h; have hv := congrArg Fin.val h; rw [tD_val, tL_val] at hv; unfold iD iL at hv; omega
  have hd : mask1 V.extra kE (tD V.extra kE) = false := by simp [mask1, tD_val]
  have hl : mask1 V.extra kE (tL V.extra kE) = false := by simp [mask1, tL_val]
  have hE := Scrub.erase_step (mask1 V.extra kE) (tD V.extra kE) (tL V.extra kE) hd hl hne (Ev cE kE base r)
    (Ev cE kE base r + 1) le_rfl (fun _ => 0) A2 (fun _ _ => rfl)
    (by
      intro i hm
      simp only [mask1, decide_eq_true_eq] at hm
      rw [hA2, if_neg hm.2.1, if_neg hm.2.2]
      by_cases h17 : i.val = 17
      · rw [if_pos h17]; simp; omega
      · rw [if_neg h17]
        by_cases hgt : iD V.extra < i.val
        · rw [if_pos hgt]; simp [CompareMachine.word]; omega
        · rw [if_neg hgt]; exact (hlen i (by omega) hm.2.1).trans hE2)
    (by rw [hA2, if_neg (by rw [tD_val]; unfold iD iL; omega), if_pos (tD_val _ _)])
    (by rw [hA2, if_pos (tL_val _ _)])
  refine hE.congr rfl ?_
  funext i
  unfold Scrub.blank s3 mask1
  by_cases h9' : i.val < 9
  · rw [if_pos h9', if_neg (by simp; omega), hA2, if_neg (by unfold iL; omega), if_neg (by unfold iD; omega),
      if_neg (by omega), if_neg (by unfold iD; omega), h9 i h9']
  · rw [if_neg h9']
    by_cases h17 : i.val < 17
    · rw [if_pos h17, if_neg (by simp; omega), hA2, if_neg (by unfold iL; omega), if_neg (by unfold iD; omega),
        if_neg (by omega), if_neg (by unfold iD; omega), hK i (by omega) (by omega)]
    · rw [if_neg h17]
      by_cases hiL : i.val = iL V.extra
      · rw [if_pos hiL, if_neg (by simp [hiL]), hA2, if_pos hiL]
      · rw [if_neg hiL]
        by_cases hiD : i.val = iD V.extra
        · rw [if_pos hiD, if_neg (by simp [hiD]), hA2, if_neg hiL, if_pos hiD]
        · rw [if_neg hiD, if_pos (by simp; omega)]

/-! ## 4. The carry walk -/

/-- The walk over a field list `fs = chainOf r`: from `s3` to `s4`. -/
theorem walk_run (r : Request) (k : rcKey a r) (hk : k ∈ rcKeys a r) (E : ℕ)
    (hW : 2 * PacketsConstruction.fieldWidth a r + 1 ≤ E) (fs : List (Fin 8)) (hfs : chainOf r = fs) :
    Step (chainM (ports V.extra kE) fs).2 (chainCost (PacketsConstruction.fieldWidth a r) fs) (fun _ => 0)
      (s3 a base V.extra kE r k E) (fun _ => 0) (s4 a base V.extra kE r k E) := by
  have hPort : ∀ f, s3 a base V.extra kE r k E ((ports V.extra kE).port f) =
      fb (PacketsConstruction.fieldWidth a r) (keyDigits a r (some k) f) := by
    intro f
    have hv : ((ports V.extra kE).port f).val = f.val + 1 := rfl
    unfold s3
    rw [if_pos (by rw [hv]; have := f.isLt; omega)]
    exact me_field r (some k) f _ hv
  have hFlag : ∀ f ∈ fs, readTapeBit (s3 a base V.extra kE r k E ((ports V.extra kE).flag f)) 0 =
      flagsOf a r (keyDigits a r (some k)) f := by
    intro f hf
    have hv : ((ports V.extra kE).flag f).val = 9 + f.val := rfl
    have h7 := chain_mem r f (by rw [hfs]; exact hf)
    unfold s3
    rw [if_neg (by rw [hv]; omega), if_pos (by rw [hv]; omega), hv, Nat.add_sub_cancel_left]
    exact cursorOuts_flag base r k f h7
  have hCap : s3 a base V.extra kE r k E (ports V.extra kE).cap = List.replicate E false := by
    have hv : (ports V.extra kE).cap.val = 17 := rfl
    unfold s3
    rw [if_neg (by rw [hv]; omega), if_neg (by rw [hv]; omega), if_neg (by rw [hv]; unfold iL; omega),
      if_neg (by rw [hv]; unfold iD; omega)]
  have hLg : s3 a base V.extra kE r k E (ports V.extra kE).lg = List.replicate E false := by
    have hv : (ports V.extra kE).lg.val = 18 := rfl
    unfold s3
    rw [if_neg (by rw [hv]; omega), if_neg (by rw [hv]; omega), if_neg (by rw [hv]; unfold iL; omega),
      if_neg (by rw [hv]; unfold iD; omega)]
  obtain ⟨A', st, hp, ho⟩ := chain_run (ports V.extra kE) (PacketsConstruction.fieldWidth a r) E
    (flagsOf a r (keyDigits a r (some k))) (fun _ => 0) (fun _ => rfl) (fun _ => rfl) rfl rfl hW fs
    (s3 a base V.extra kE r k E) (keyDigits a r (some k)) hPort hFlag hCap hLg (fun f => digit_fit r k hk f)
  refine st.congr rfl ?_
  funext i
  unfold s4
  by_cases hi : 1 ≤ i.val ∧ i.val ≤ 8
  · rw [dif_pos hi]
    have e1 : (ports V.extra kE).port ⟨i.val - 1, by omega⟩ = i := Fin.ext (by
      change i.val - 1 + 1 = i.val; omega)
    have hp' := hp ⟨i.val - 1, by omega⟩
    rw [e1] at hp'
    rw [hp', ← hfs, chain_succ a r k]
  · rw [dif_neg hi]
    refine ho i (fun f hf => hi ?_)
    have hv : f.val + 1 = i.val := congrArg Fin.val hf
    have := f.isLt
    omega

theorem kind_read (r : Request) (k : rcKey a r) (E : ℕ) :
    s3 a base V.extra kE r k E (tK V.extra kE) = List.replicate (thrFlag r) true := by
  unfold s3
  rw [if_neg (by rw [tK_val]; omega), if_pos (by rw [tK_val]; omega), tK_val]
  exact cursorOuts_kind base r k

/-- **The carry walk, switched on the kind bit.** -/
theorem run4 (r : Request) (k : rcKey a r) (hk : k ∈ rcKeys a r) (E : ℕ)
    (hW : 2 * PacketsConstruction.fieldWidth a r + 1 ≤ E) :
    Step (st4 V kE) (chainCost (PacketsConstruction.fieldWidth a r) (chainOf r) + 2) (fun _ => 0)
      (s3 a base V.extra kE r k E) (fun _ => 0) (s4 a base V.extra kE r k E) := by
  by_cases hthr : thrFlag r = 1
  · have hco : chainOf r = thrChain := by simp [chainOf, hthr]
    have hb : readTapeBit (s3 a base V.extra kE r k E (tK V.extra kE)) ((fun _ => 0) (tK V.extra kE)) = true := by
      rw [kind_read, hthr]; rfl
    rw [hco]
    exact CloseoutRowsOriginalSwitch.true_run _ _ _ (walk_run V kE r k hk E hW thrChain hco) hb
  · have hco : chainOf r = symChain := by simp [chainOf, hthr]
    have h0 : thrFlag r = 0 := by have := thrFlag_le r; omega
    have hb : readTapeBit (s3 a base V.extra kE r k E (tK V.extra kE)) ((fun _ => 0) (tK V.extra kE)) = false := by
      rw [kind_read, h0]; rfl
    rw [hco]
    exact CloseoutRowsOriginalSwitch.false_run _ _ _ (walk_run V kE r k hk E hW symChain hco) hb

/-! ## 5. Erase the flags and the kind; 6. erase the driver -/

theorem run5 (r : Request) (k : rcKey a r) (E : ℕ) (hE : 1 ≤ E) :
    Step (st5 V kE) (2 * E + 4) (fun _ => 0) (s4 a base V.extra kE r k E) (fun _ => 0)
      (s5 a base V.extra kE r k E) := by
  have hne : tD V.extra kE ≠ tL V.extra kE := by
    intro h; have hv := congrArg Fin.val h; rw [tD_val, tL_val] at hv; unfold iD iL at hv; omega
  have hd : mask2 V.extra kE (tD V.extra kE) = false := by
    simp only [mask2, tD_val, decide_eq_false_iff_not]; unfold iD; omega
  have hl : mask2 V.extra kE (tL V.extra kE) = false := by
    simp only [mask2, tL_val, decide_eq_false_iff_not]; unfold iL; omega
  have hs4 : ∀ i : Fin (TS V.extra kE), ¬ (1 ≤ i.val ∧ i.val ≤ 8) →
      s4 a base V.extra kE r k E i = s3 a base V.extra kE r k E i := fun i hi => by unfold s4; rw [dif_neg hi]
  have hE' := Scrub.erase_step (mask2 V.extra kE) (tD V.extra kE) (tL V.extra kE) hd hl hne E (E + 1) le_rfl
    (fun _ => 0) (s4 a base V.extra kE r k E) (fun _ _ => rfl)
    (by
      intro i hm
      simp only [mask2, decide_eq_true_eq] at hm
      rw [hs4 i (by omega)]
      unfold s3
      rw [if_neg (by omega), if_pos hm.2]
      exact (cursorOuts_len base _ (by omega) r k).trans hE)
    (by
      rw [hs4 _ (by rw [tD_val]; unfold iD; omega)]
      unfold s3
      rw [if_neg (by rw [tD_val]; unfold iD; omega), if_neg (by rw [tD_val]; unfold iD; omega),
        if_neg (by rw [tD_val]; unfold iD iL; omega), if_pos (tD_val _ _)])
    (by
      rw [hs4 _ (by rw [tL_val]; unfold iL; omega)]
      unfold s3
      rw [if_neg (by rw [tL_val]; unfold iL; omega), if_neg (by rw [tL_val]; unfold iL; omega), if_pos (tL_val _ _)])
  refine hE'.congr rfl ?_
  funext i
  unfold Scrub.blank s5 mask2
  by_cases hm : 9 ≤ i.val ∧ i.val < 17
  · rw [if_pos (by simp [hm]), if_pos hm]
  · rw [if_neg (by simp; omega), if_neg hm]

theorem run6 (r : Request) (k : rcKey a r) (E : ℕ) :
    Step (st6 V kE) (2 * E + 2) (fun _ => 0) (s5 a base V.extra kE r k E) (fun _ => 0)
      (sExit a base V.extra kE r k E) := by
  have hinj : Function.Injective (fun _ : Fin 1 => tD V.extra kE) := fun x y _ => Subsingleton.elim x y
  obtain ⟨H6, A6, s6, hs, ho⟩ := Dock.lift (DErase.run E) (fun _ : Fin 1 => tD V.extra kE) hinj (fun _ => 0)
    (fun _ => 0) (s5 a base V.extra kE r k E) (by
      intro j
      refine ⟨rfl, ?_⟩
      rw [ZeroPadding.pad_zero]
      unfold s5 s4 s3
      rw [if_neg (by rw [tD_val]; unfold iD; omega), dif_neg (by rw [tD_val]; unfold iD; omega),
        if_neg (by rw [tD_val]; unfold iD; omega), if_neg (by rw [tD_val]; unfold iD; omega),
        if_neg (by rw [tD_val]; unfold iD iL; omega), if_pos (tD_val _ _)])
  have hH : H6 = fun _ => 0 := by
    funext i
    by_cases hi : i = tD V.extra kE
    · rw [hi]; exact (hs 0).1
    · exact (ho i (fun _ h => hi h.symm)).1
  refine s6.congr hH ?_
  funext i
  unfold sExit
  by_cases hi : i.val = iD V.extra
  · have e : i = tD V.extra kE := Fin.ext hi
    rw [if_pos hi, e, (hs 0).2, ZeroPadding.pad_zero]
  · rw [if_neg hi]
    exact (ho i (fun _ h => hi (by rw [← h]; rfl))).2

end Runs

end
end NearCubicWires.PacketsConstruction.Cursor

import Proof.SourceAssembly.SourceInitEnc

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open NearCubicWires.SupplierEstimator
namespace NearCubicWires.SourceConstruction.InitPost
noncomputable section

/-! ## 1. The docks -/

def rw7 : Fin 7 → Fin 323 := ![2, 8, 6, 9, 10, 7, 11]
def rc79 : Fin 79 → Fin 323 := fun j =>
  ⟨if j.val = 0 then 0 else if j.val = 47 then 18 else if j.val = 77 then 12 else 32 + j.val, by
    have := j.isLt; split_ifs <;> omega⟩
def sl57 : Fin 57 → Fin 323 := fun j =>
  ⟨if j.val = 0 then 0 else if j.val = 1 then 18 else if j.val = 49 then 21 else if j.val = 55 then 17
    else 111 + j.val, by have := j.isLt; split_ifs <;> omega⟩
def en119 : Fin 119 → Fin 323 := fun j =>
  ⟨if j.val = 0 then 1 else if j.val = 17 then 22 else if j.val = 40 then 25 else if j.val = 43 then 26
    else if j.val = 37 then 27 else if j.val = 77 then 28 else if j.val = 116 then 29
    else if j.val = 97 then 30 else if j.val = 117 then 31 else 168 + j.val, by
    have := j.isLt; split_ifs <;> omega⟩
def cp4 : Fin 4 → Fin 323 := ![1, 287, 20, 288]
def un43 : Fin 43 → Fin 323 := fun j =>
  ⟨if j.val = 0 then 2 else if j.val = 1 then 3 else if j.val = 2 then 1 else if j.val ≤ 6 then 10 + j.val
    else if j.val ≤ 40 then 282 + j.val else if j.val = 41 then 4 else 5, by
    have := j.isLt; split_ifs <;> omega⟩

theorem rw7_inj : Function.Injective rw7 := by decide
theorem cp4_inj : Function.Injective cp4 := by decide

macro "injv2" : tactic => `(tactic| (
  intro a b hab
  have hv := congrArg Fin.val hab
  have ha := a.isLt
  have hb := b.isLt
  simp only [rc79, sl57, un43] at hv
  apply Fin.ext
  split_ifs at hv <;> omega))

theorem rc79_inj : Function.Injective rc79 := by injv2
theorem sl57_inj : Function.Injective sl57 := by injv2
theorem un43_inj : Function.Injective un43 := by injv2

/-- A left inverse of `en119` on values (ten branches instead of a hundred). -/
def enDec (v : ℕ) : ℕ :=
  if v = 1 then 0 else if v = 22 then 17 else if v = 25 then 40 else if v = 26 then 43 else if v = 27 then 37
  else if v = 28 then 77 else if v = 29 then 116 else if v = 30 then 97 else if v = 31 then 117 else v - 168

theorem en119_dec (j : Fin 119) : enDec (en119 j).val = j.val := by
  have := j.isLt
  simp only [en119]
  split_ifs with h0 h17 h40 h43 h37 h77 h116 h97 h117
  · rw [h0]; rfl
  · rw [h17]; rfl
  · rw [h40]; rfl
  · rw [h43]; rfl
  · rw [h37]; rfl
  · rw [h77]; rfl
  · rw [h116]; rfl
  · rw [h97]; rfl
  · rw [h117]; rfl
  · unfold enDec
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    omega

theorem en119_inj : Function.Injective en119 := by
  intro a b h
  have e := congrArg (fun x : Fin 323 => enDec x.val) h
  simp only [en119_dec] at e
  exact Fin.ext e

/-- Where each dock writes, by value. -/
theorem rw7_val (j : Fin 7) : (rw7 j).val = 2 ∨ (6 ≤ (rw7 j).val ∧ (rw7 j).val < 12) := by
  fin_cases j <;> simp [rw7]
theorem rc79_val (j : Fin 79) : (rc79 j).val = 0 ∨ (rc79 j).val = 18 ∨ (rc79 j).val = 12 ∨
    (33 ≤ (rc79 j).val ∧ (rc79 j).val < 111) := by
  have := j.isLt; simp only [rc79]; split_ifs <;> omega
theorem sl57_val (j : Fin 57) : (sl57 j).val = 0 ∨ (sl57 j).val = 18 ∨ (sl57 j).val = 21 ∨
    (sl57 j).val = 17 ∨ (112 ≤ (sl57 j).val ∧ (sl57 j).val < 168) := by
  have := j.isLt; simp only [sl57]; split_ifs <;> omega
theorem en119_val (j : Fin 119) : (en119 j).val = 1 ∨ (en119 j).val = 22 ∨
    (25 ≤ (en119 j).val ∧ (en119 j).val ≤ 31) ∨ (169 ≤ (en119 j).val ∧ (en119 j).val < 287) := by
  have := j.isLt; simp only [en119]; split_ifs <;> omega
theorem cp4_val (j : Fin 4) : (cp4 j).val = 1 ∨ (cp4 j).val = 20 ∨ (cp4 j).val = 287 ∨ (cp4 j).val = 288 := by
  fin_cases j <;> simp [cp4]
theorem un43_val (j : Fin 43) : (un43 j).val = 1 ∨ (2 ≤ (un43 j).val ∧ (un43 j).val ≤ 5) ∨
    (13 ≤ (un43 j).val ∧ (un43 j).val ≤ 16) ∨ (289 ≤ (un43 j).val ∧ (un43 j).val < 323) := by
  have := j.isLt; simp only [un43]; split_ifs <;> omega

/-! ## 2. The machine, the input, the cost -/

def input (q b V VL Rc : ℕ) : Fin 323 → List Bool := fun i =>
  if i.val = 0 then UnaryTemplate.tape q
  else if i.val = 1 then List.replicate b true
  else if i.val = 2 then List.replicate V true
  else if i.val = 3 then List.replicate VL false
  else if i.val = 4 then List.replicate Rc true
  else if i.val = 5 then List.replicate (Rc+2) false
  else if i.val < 12 then []
  else List.replicate Rc false

def machine (L cS cR : ℕ) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine rw7 RewindOnce.machine)
    (RecoveryFocus.machine rc79 (RowConst.machine L 2)))
    (RecoveryFocus.machine sl57 (InitSlopes.machine L)))
    (RecoveryFocus.machine en119 InitEnc.machine))
    (RecoveryFocus.machine cp4 ClockUnarySum.machine))
    (RecoveryFocus.machine un43 (Uniform.machine cS cR))

/-- The small slope `Ms = 2(K+1)`. -/
abbrev Ms (L q : ℕ) : ℕ := 2*(normalizedLiveCount q L+1)

def cost (L cS cR q b V Rc : ℕ) : ℕ :=
  ((((RewindOnce.cost V+1+RowConst.cost L 2 q)+1+InitSlopes.cost L q (Ms L q))+1+InitEnc.cost b)+1+
    (2*b+6))+1+Uniform.cost cS cR V b Rc

/-- The exit heads: the four drivers at `1`, everything else at `0`. -/
abbrev outH : Fin 323 → ℕ := dockH un43 (fun _ => 0) Uniform.outH

theorem outH_val (i : Fin 323) : outH i = if 13 ≤ i.val ∧ i.val ≤ 16 then 1 else 0 := by
  show dockH un43 (fun _ => 0) Uniform.outH i = _
  by_cases h : ∃ j, un43 j = i
  · obtain ⟨j, rfl⟩ := h
    rw [dockH_slot un43 un43_inj]
    have := j.isLt
    simp only [Uniform.outH, un43, Fin.val_mk]
    split_ifs <;> omega
  · rw [dockH_other un43 _ _ i (fun j hj => h ⟨j, hj⟩)]
    have hn : ¬ (13 ≤ i.val ∧ i.val ≤ 16) := by
      intro hi
      exact h ⟨⟨i.val - 10, by omega⟩, Fin.ext (by simp only [un43]; split_ifs <;> omega)⟩
    rw [if_neg hn]

/-! ## 3. The copy of `1^b`, padded off its source -/

theorem stepCopyB (b Rc : ℕ) : Step ClockUnarySum.machine (2*b+6) (fun _ => 0)
    ![List.replicate b true, ZeroPadding.pad Rc [], ZeroPadding.pad Rc [], ZeroPadding.pad Rc []] (fun _ => 0)
    ![List.replicate b true, ZeroPadding.pad Rc [], ZeroPadding.pad Rc (List.replicate b true),
      ZeroPadding.pad Rc (List.replicate (b+2) false)] := by
  have h := (BlockPlatform.UnaryCalc.copy_step b).pad ![0, Rc, Rc, Rc]
  refine (h.congr_in rfl ?_).congr rfl ?_
  · funext i; fin_cases i
    · exact ZeroPadding.pad_zero _
    · rfl
    · rfl
    · rfl
  · funext i; fin_cases i
    · exact ZeroPadding.pad_zero _
    · rfl
    · rfl
    · rfl

/-! ## 4. The run -/

/-- **Everything after `Once`, as one fixed machine.** From `input q b V VL Rc` (heads `0`), with
`V ≤ Rc`, `VL ≤ Rc` (`Uniform`'s erase) and `1 ≤ Rc`, the run reaches heads `outH` and:
- the arity, `1^b`, the clear driver and log unchanged (tapes 0, 1, 4, 5);
- the rewind driver `1^V` (6) and log `0^V` (7);
- `U0` (12) and the drivers `S R B v` as padded templates (13..16, heads `1`);
- `Mb = (q/(200(K+2)))·Ms`, `Ms = 2(K+1)`, `1^b`, `1^q`, each padded by `Rc` (17, 18, 20, 21), and
  tape 19 (`curT`) blank;
- the eight `enc`/`app` constants padded by `Rc` (22, 25..31), tapes 23, 24 blank;
- `1^V` and its log erased to `0^Rc` (2, 3);
- every tape from 12 on of length `≥ Rc`. -/
theorem post_run (L cS cR q b V VL Rc : ℕ) (hV : V ≤ Rc) (hVL : VL ≤ Rc) (hRc : 1 ≤ Rc) :
    ∃ W : Fin 323 → List Bool,
      Step (machine L cS cR) (cost L cS cR q b V Rc) (fun _ => 0) (input q b V VL Rc) outH W ∧
      W 0 = UnaryTemplate.tape q ∧ W 1 = List.replicate b true ∧
      W 4 = List.replicate Rc true ∧ W 5 = List.replicate (Rc+2) false ∧
      W 6 = List.replicate V true ∧ W 7 = List.replicate V false ∧
      W 12 = ZeroPadding.pad Rc (List.replicate (3*(normalizedLiveCount q L+2+1) +
        ((q - normalizedLiveCount q L+1)/2 + (q - normalizedLiveCount q L+1)/2)) true) ∧
      W 13 = ZeroPadding.pad Rc (UnaryTemplate.tape (cS*(V+1))) ∧
      W 14 = ZeroPadding.pad Rc (UnaryTemplate.tape (cR*(V+1))) ∧
      W 15 = ZeroPadding.pad Rc (UnaryTemplate.tape (V+1)) ∧
      W 16 = ZeroPadding.pad Rc (UnaryTemplate.tape b) ∧
      W 17 = ZeroPadding.pad Rc (List.replicate (q / InitSlopes.dv L q * Ms L q) true) ∧
      W 18 = ZeroPadding.pad Rc (List.replicate (Ms L q) true) ∧
      W 19 = List.replicate Rc false ∧
      W 20 = ZeroPadding.pad Rc (List.replicate b true) ∧
      W 21 = ZeroPadding.pad Rc (List.replicate q true) ∧
      W 22 = ZeroPadding.pad Rc (frame (SignedSortKey.binary (2*b+2) 0)) ∧
      W 23 = List.replicate Rc false ∧ W 24 = List.replicate Rc false ∧
      W 25 = ZeroPadding.pad Rc (List.replicate (InitEnc.rr b+2) false) ∧
      W 26 = ZeroPadding.pad Rc (List.replicate (InitEnc.rr b+1) true) ∧
      W 27 = ZeroPadding.pad Rc (List.replicate (InitEnc.rr b+2) false) ∧
      W 28 = ZeroPadding.pad Rc (List.replicate (40*b+56) false) ∧
      W 29 = ZeroPadding.pad Rc (List.replicate (CloseoutFinalC10AppendWorkspaceInit.capacity b) false) ∧
      W 30 = ZeroPadding.pad Rc (UnaryTemplate.tape (20*b+22)) ∧
      W 31 = ZeroPadding.pad Rc (List.replicate (CloseoutFinalC10AppendWorkspaceInit.capacity b) false) ∧
      W 2 = List.replicate Rc false ∧ W 3 = List.replicate Rc false ∧
      (∀ i : Fin 323, 12 ≤ i.val → Rc ≤ (W i).length) := by
  let E : Fin 323 → Prop := fun i => i.val < 12
  let B0 := input q b V VL Rc
  have L0 : ∀ i, ¬ E i → Rc ≤ (B0 i).length := by
    intro i hi
    simp only [E, not_lt] at hi
    simp only [B0, input, if_neg (show i.val ≠ 0 by omega), if_neg (show i.val ≠ 1 by omega),
      if_neg (show i.val ≠ 2 by omega), if_neg (show i.val ≠ 3 by omega), if_neg (show i.val ≠ 4 by omega),
      if_neg (show i.val ≠ 5 by omega), if_neg (show ¬ i.val < 12 by omega), List.length_replicate]
    exact le_rfl
  have bl0 : ∀ i : Fin 323, 12 ≤ i.val → B0 i = ZeroPadding.pad Rc [] := by
    intro i hi
    rw [← Uniform.pad_blank]
    simp only [B0, input, if_neg (show i.val ≠ 0 by omega), if_neg (show i.val ≠ 1 by omega),
      if_neg (show i.val ≠ 2 by omega), if_neg (show i.val ≠ 3 by omega), if_neg (show i.val ≠ 4 by omega),
      if_neg (show i.val ≠ 5 by omega), if_neg (show ¬ i.val < 12 by omega)]
  have B0_0 : B0 0 = UnaryTemplate.tape q := rfl
  have B0_1 : B0 1 = List.replicate b true := rfl
  have B0_2 : B0 2 = List.replicate V true := rfl
  have B0_3 : B0 3 = List.replicate VL false := rfl
  have B0_4 : B0 4 = List.replicate Rc true := rfl
  have B0_5 : B0 5 = List.replicate (Rc+2) false := rfl
  have B0_low : ∀ i : Fin 323, 6 ≤ i.val → i.val < 12 → B0 i = [] := by
    intro i h1 h2
    simp only [B0, input, if_neg (show i.val ≠ 0 by omega), if_neg (show i.val ≠ 1 by omega),
      if_neg (show i.val ≠ 2 by omega), if_neg (show i.val ≠ 3 by omega), if_neg (show i.val ≠ 4 by omega),
      if_neg (show i.val ≠ 5 by omega), if_pos h2]
  -- 1: the rewind tapes
  obtain ⟨W1, h1s, h12, h15, h10⟩ := RewindOnce.rewind_run V
  have st1 := Dimension.dock0 h1s rw7 rw7_inj B0 (by
    intro j
    fin_cases j
    · exact B0_2
    · exact B0_low 8 (by decide) (by decide)
    · exact B0_low 6 (by decide) (by decide)
    · exact B0_low 9 (by decide) (by decide)
    · exact B0_low 10 (by decide) (by decide)
    · exact B0_low 7 (by decide) (by decide)
    · exact B0_low 11 (by decide) (by decide))
  let B1 := install rw7 B0 W1
  have L1 := RowConst.long_install rw7 rw7_inj B0 W1 E Rc L0 (by
    intro j hj
    exfalso; apply hj
    rcases rw7_val j with h | h <;> simp only [E] <;> omega)
  have B1off : ∀ i : Fin 323, i.val ≠ 2 → (i.val < 6 ∨ 12 ≤ i.val) → B1 i = B0 i := by
    intro i h1 h2
    refine install_other rw7 B0 W1 i (fun j hj => ?_)
    have := congrArg Fin.val hj
    rcases rw7_val j with h | h <;> omega
  have B1_2 : B1 2 = List.replicate V true := (install_slot rw7 rw7_inj B0 W1 0).trans h10
  have B1_6 : B1 6 = List.replicate V true := (install_slot rw7 rw7_inj B0 W1 2).trans h12
  have B1_7 : B1 7 = List.replicate V false := (install_slot rw7 rw7_inj B0 W1 5).trans h15
  have B1blank : ∀ i : Fin 323, 12 ≤ i.val → B1 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B1off i (by omega) (Or.inr hi)).trans (bl0 i hi)
  
  obtain ⟨W2, h2s, h247, h277, h20, h2l⟩ := RowConst.const_run L 2 q Rc
  have st2 := Dimension.dock0 h2s rc79 rc79_inj B1 (by
    intro j
    by_cases hj : j.val = 0
    · have e : rc79 j = 0 := Fin.ext (by simp [rc79, hj])
      rw [e]
      simp only [RowConst.input, if_pos hj]
      exact (B1off 0 (by decide) (Or.inl (by decide))).trans B0_0
    · simp only [RowConst.input, if_neg hj]
      exact B1blank _ (by have := rc79_val j; simp only [rc79, hj, if_false] at this ⊢; split_ifs <;> omega))
  let B2 := install rc79 B1 W2
  have L2 := RowConst.long_install rc79 rc79_inj B1 W2 E Rc L1 (by
    intro j hj
    by_cases h0 : j.val = 0
    · exfalso; apply hj; simp only [E, rc79, h0, if_true]; omega
    · exact h2l j h0)
  have B2off : ∀ i : Fin 323, i.val ≠ 0 → i.val ≠ 18 → i.val ≠ 12 → (i.val < 33 ∨ 111 ≤ i.val) →
      B2 i = B1 i := by
    intro i h1 h2 h3 h4
    refine install_other rc79 B1 W2 i (fun j hj => ?_)
    have := congrArg Fin.val hj
    rcases rc79_val j with h | h | h | h <;> omega
  have B2_0 : B2 0 = UnaryTemplate.tape q := (install_slot rc79 rc79_inj B1 W2 0).trans h20
  have B2_18 : B2 18 = ZeroPadding.pad Rc (List.replicate (Ms L q) true) :=
    (install_slot rc79 rc79_inj B1 W2 47).trans h247
  have B2_12 := (install_slot rc79 rc79_inj B1 W2 77).trans h277
  -- 3: the slopes `1^q`, `1^Mb`
  obtain ⟨W3, h3s, h30, h31, h349, h355, h3l⟩ := InitSlopes.slopes_run L q (Ms L q) Rc
  have st3 := Dimension.dock0 h3s sl57 sl57_inj B2 (by
    intro j
    by_cases hj0 : j.val = 0
    · have e : sl57 j = 0 := Fin.ext (by simp [sl57, hj0])
      rw [e]; simp only [InitSlopes.input, if_pos hj0]; exact B2_0
    · by_cases hj1 : j.val = 1
      · have e : sl57 j = 18 := Fin.ext (by simp [sl57, hj1])
        rw [e]; simp only [InitSlopes.input, if_neg hj0, if_pos hj1]; exact B2_18
      · simp only [InitSlopes.input, if_neg hj0, if_neg hj1]
        have hv := sl57_val j
        have h0' : (sl57 j).val ≠ 0 := by simp only [sl57, if_neg hj0]; split_ifs <;> omega
        have h18 : (sl57 j).val ≠ 18 := by simp only [sl57, if_neg hj0, if_neg hj1]; split_ifs <;> omega
        exact (B2off _ h0' h18 (by omega) (by omega)).trans (B1blank _ (by omega)))
  let B3 := install sl57 B2 W3
  have L3 := RowConst.long_install sl57 sl57_inj B2 W3 E Rc L2 (by
    intro j hj
    by_cases h0 : j.val = 0
    · exfalso; apply hj; simp only [E, sl57, h0, if_true]; omega
    · exact h3l j h0)
  have B3off : ∀ i : Fin 323, i.val ≠ 0 → i.val ≠ 18 → i.val ≠ 21 → i.val ≠ 17 →
      (i.val < 112 ∨ 168 ≤ i.val) → B3 i = B2 i := by
    intro i h1 h2 h3 h4 h5
    refine install_other sl57 B2 W3 i (fun j hj => ?_)
    have := congrArg Fin.val hj
    rcases sl57_val j with h | h | h | h | h <;> omega
  have B3_0 : B3 0 = UnaryTemplate.tape q := (install_slot sl57 sl57_inj B2 W3 0).trans h30
  have B3_18 : B3 18 = ZeroPadding.pad Rc (List.replicate (Ms L q) true) :=
    (install_slot sl57 sl57_inj B2 W3 1).trans h31
  have B3_21 : B3 21 = ZeroPadding.pad Rc (List.replicate q true) :=
    (install_slot sl57 sl57_inj B2 W3 49).trans h349
  have B3_17 : B3 17 = ZeroPadding.pad Rc (List.replicate (q / InitSlopes.dv L q * Ms L q) true) :=
    (install_slot sl57 sl57_inj B2 W3 55).trans h355
  -- the tapes untouched by stages 1..3
  have B3_orig : ∀ i : Fin 323, 12 ≤ i.val → i.val ≠ 12 → i.val ≠ 17 → i.val ≠ 18 → i.val ≠ 21 →
      (i.val < 33 ∨ 168 ≤ i.val) → B3 i = ZeroPadding.pad Rc [] := by
    intro i h1 h2 h3 h4 h5 h6
    rw [B3off i (by omega) h4 h5 h3 (by omega), B2off i (by omega) h4 h2 (by omega)]
    exact B1blank i h1
  have B3_1 : B3 1 = List.replicate b true := by
    rw [B3off 1 (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide)),
      B2off 1 (by decide) (by decide) (by decide) (Or.inl (by decide)),
      B1off 1 (by decide) (Or.inl (by decide))]
    exact B0_1
  -- 4: the `enc`/`app` constants
  obtain ⟨W4, h4s, h40, h417, h440, h443, h437, h477, h4116, h497, h4117, h4l⟩ := InitEnc.enc_run b Rc hRc
  have st4 := Dimension.dock0 h4s en119 en119_inj B3 (by
    intro j
    by_cases hj0 : j.val = 0
    · have e : en119 j = 1 := Fin.ext (by simp [en119, hj0])
      rw [e]; simp only [InitEnc.input, if_pos hj0]; exact B3_1
    · simp only [InitEnc.input, if_neg hj0]
      have hv := en119_val j
      have h1 : (en119 j).val ≠ 1 := by simp only [en119, if_neg hj0]; split_ifs <;> omega
      exact B3_orig _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  let B4 := install en119 B3 W4
  have L4 := RowConst.long_install en119 en119_inj B3 W4 E Rc L3 (by
    intro j hj
    by_cases h0 : j.val = 0
    · exfalso; apply hj; simp only [E, en119, h0, if_true]; omega
    · exact h4l j h0)
  have B4off : ∀ i : Fin 323, i.val ≠ 1 → i.val ≠ 22 → (i.val < 25 ∨ 31 < i.val) →
      (i.val < 169 ∨ 287 ≤ i.val) → B4 i = B3 i := by
    intro i h1 h2 h3 h4
    refine install_other en119 B3 W4 i (fun j hj => ?_)
    have := congrArg Fin.val hj
    rcases en119_val j with h | h | h | h <;> omega
  have B4_1 : B4 1 = List.replicate b true := (install_slot en119 en119_inj B3 W4 0).trans h40
  have B4_22 := (install_slot en119 en119_inj B3 W4 17).trans h417
  have B4_25 := (install_slot en119 en119_inj B3 W4 40).trans h440
  have B4_26 := (install_slot en119 en119_inj B3 W4 43).trans h443
  have B4_27 := (install_slot en119 en119_inj B3 W4 37).trans h437
  have B4_28 := (install_slot en119 en119_inj B3 W4 77).trans h477
  have B4_29 := (install_slot en119 en119_inj B3 W4 116).trans h4116
  have B4_30 := (install_slot en119 en119_inj B3 W4 97).trans h497
  have B4_31 := (install_slot en119 en119_inj B3 W4 117).trans h4117
  -- 5: the copy of `1^b`
  let o5 : Fin 4 → List Bool := ![List.replicate b true, ZeroPadding.pad Rc [],
    ZeroPadding.pad Rc (List.replicate b true), ZeroPadding.pad Rc (List.replicate (b+2) false)]
  have st5 := Dimension.dock0 (stepCopyB b Rc) cp4 cp4_inj B4 (by
    intro j
    fin_cases j
    · exact B4_1
    · exact (B4off 287 (by decide) (by decide) (Or.inr (by decide)) (Or.inr (by decide))).trans
        (B3_orig 287 (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide)))
    · exact (B4off 20 (by decide) (by decide) (Or.inl (by decide)) (Or.inl (by decide))).trans
        (B3_orig 20 (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide)))
    · exact (B4off 288 (by decide) (by decide) (Or.inr (by decide)) (Or.inr (by decide))).trans
        (B3_orig 288 (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide))))
  let B5 := install cp4 B4 o5
  have L5 := RowConst.long_install cp4 cp4_inj B4 o5 E Rc L4 (by
    intro j hj
    fin_cases j
    · exfalso; apply hj; simp [E, cp4]
    all_goals exact Uniform.long_pad Rc _)
  have B5off : ∀ i : Fin 323, i.val ≠ 1 → i.val ≠ 20 → i.val ≠ 287 → i.val ≠ 288 → B5 i = B4 i := by
    intro i h1 h2 h3 h4
    refine install_other cp4 B4 o5 i (fun j hj => ?_)
    have := congrArg Fin.val hj
    rcases cp4_val j with h | h | h | h <;> omega
  have B5_1 : B5 1 = List.replicate b true := install_slot cp4 cp4_inj B4 o5 0
  have B5_20 : B5 20 = ZeroPadding.pad Rc (List.replicate b true) := install_slot cp4 cp4_inj B4 o5 2
  -- the tapes untouched by stages 2..5, back to stage 1
  have B5_to1 : ∀ i : Fin 323, ((2 ≤ i.val ∧ i.val < 12) ∨ (13 ≤ i.val ∧ i.val < 17) ∨ 289 ≤ i.val) →
      B5 i = B1 i := by
    intro i hi
    rw [B5off i (by omega) (by omega) (by omega) (by omega), B4off i (by omega) (by omega) (by omega) (by omega),
      B3off i (by omega) (by omega) (by omega) (by omega) (by omega),
      B2off i (by omega) (by omega) (by omega) (by omega)]
  -- 6: the uniform drivers (heads to `1`)
  obtain ⟨W6, h6s, h63, h64, h65, h66, h60, h61, h62, h641, h642, h6l⟩ :=
    Uniform.uniform_run cS cR V VL b Rc hV hVL
  have st6 := h6s.dock un43 un43_inj (fun _ => 0) B5 (fun _ => rfl) (by
    intro j
    have hj := j.isLt
    by_cases h0 : j.val = 0
    · have e : un43 j = 2 := Fin.ext (by simp [un43, h0])
      rw [e, B5_to1 2 (Or.inl ⟨by decide, by decide⟩), B1_2]
      simp only [Uniform.input, if_pos h0]
    · by_cases h1 : j.val = 1
      · have e : un43 j = 3 := Fin.ext (by simp [un43, h1])
        rw [e, B5_to1 3 (Or.inl ⟨by decide, by decide⟩), B1off 3 (by decide) (Or.inl (by decide)), B0_3]
        simp only [Uniform.input, if_neg h0, if_pos h1]
      · by_cases h2 : j.val = 2
        · have e : un43 j = 1 := Fin.ext (by simp [un43, h2])
          rw [e, B5_1]
          simp only [Uniform.input, if_neg h0, if_neg h1, if_pos h2]
        · by_cases h41 : j.val = 41
          · have e : un43 j = 4 := Fin.ext (by simp [un43, h41])
            rw [e, B5_to1 4 (Or.inl ⟨by decide, by decide⟩), B1off 4 (by decide) (Or.inl (by decide)), B0_4]
            simp only [Uniform.input, if_neg h0, if_neg h1, if_neg h2, if_pos h41]
          · by_cases h42 : j.val = 42
            · have e : un43 j = 5 := Fin.ext (by simp [un43, h42])
              rw [e, B5_to1 5 (Or.inl ⟨by decide, by decide⟩), B1off 5 (by decide) (Or.inl (by decide)), B0_5]
              simp only [Uniform.input, if_neg h0, if_neg h1, if_neg h2, if_neg h41, if_pos h42]
            · have hv : (un43 j).val = (if j.val ≤ 6 then 10 + j.val else 282 + j.val) := by
                simp only [un43, if_neg h0, if_neg h1, if_neg h2]
                split_ifs <;> omega
              have hr : (13 ≤ (un43 j).val ∧ (un43 j).val < 17) ∨ 289 ≤ (un43 j).val := by
                split_ifs at hv <;> omega
              simp only [Uniform.input, if_neg h0, if_neg h1, if_neg h2, if_neg h41, if_neg h42]
              rw [B5_to1 _ (Or.inr hr), B1blank _ (by omega), ← Uniform.pad_blank])
  let B6 := install un43 B5 W6
  have L6 := RowConst.long_install un43 un43_inj B5 W6 E Rc L5 (by
    intro j hj
    by_cases h2 : j.val = 2
    · exfalso; apply hj; simp only [E, un43, h2]; decide
    · exact h6l j h2)
  have B6off : ∀ i : Fin 323, i.val ≠ 1 → (i.val < 2 ∨ 5 < i.val) → (i.val < 13 ∨ 16 < i.val) →
      i.val < 289 → B6 i = B5 i := by
    intro i h1 h2 h3 h4
    refine install_other un43 B5 W6 i (fun j hj => ?_)
    have := congrArg Fin.val hj
    rcases un43_val j with h | h | h | h <;> omega
  -- the tapes from 12 to 31 (not 13..16, 20), back to stage 4
  have c64 : ∀ i : Fin 323, 17 ≤ i.val → i.val ≤ 31 → i.val ≠ 20 → B6 i = B4 i := by
    intro i h1 h2 h3
    rw [B6off i (by omega) (by omega) (by omega) (by omega), B5off i (by omega) h3 (by omega) (by omega)]
  have c43 : ∀ i : Fin 323, 12 ≤ i.val → i.val ≤ 24 → i.val ≠ 22 → B4 i = B3 i := by
    intro i h1 h2 h3
    exact B4off i (by omega) h3 (Or.inl (by omega)) (Or.inl (by omega))
  refine ⟨B6, ((((st1.seq st2).seq st3).seq st4).seq st5).seq st6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [B6off 0 (by decide) (Or.inl (by decide)) (Or.inl (by decide)) (by decide),
      B5off 0 (by decide) (by decide) (by decide) (by decide),
      B4off 0 (by decide) (by decide) (Or.inl (by decide)) (Or.inl (by decide))]
    exact B3_0
  · exact (install_slot un43 un43_inj B5 W6 2).trans h62
  · exact (install_slot un43 un43_inj B5 W6 41).trans h641
  · exact (install_slot un43 un43_inj B5 W6 42).trans h642
  · rw [B6off 6 (by decide) (Or.inr (by decide)) (Or.inl (by decide)) (by decide),
      B5_to1 6 (Or.inl ⟨by decide, by decide⟩)]
    exact B1_6
  · rw [B6off 7 (by decide) (Or.inr (by decide)) (Or.inl (by decide)) (by decide),
      B5_to1 7 (Or.inl ⟨by decide, by decide⟩)]
    exact B1_7
  · rw [B6off 12 (by decide) (Or.inr (by decide)) (Or.inl (by decide)) (by decide),
      B5off 12 (by decide) (by decide) (by decide) (by decide), c43 12 (by decide) (by decide) (by decide),
      B3off 12 (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))]
    exact B2_12
  · exact (install_slot un43 un43_inj B5 W6 3).trans h63
  · exact (install_slot un43 un43_inj B5 W6 4).trans h64
  · exact (install_slot un43 un43_inj B5 W6 5).trans h65
  · exact (install_slot un43 un43_inj B5 W6 6).trans h66
  · rw [c64 17 (by decide) (by decide) (by decide), c43 17 (by decide) (by decide) (by decide)]
    exact B3_17
  · rw [c64 18 (by decide) (by decide) (by decide), c43 18 (by decide) (by decide) (by decide)]
    exact B3_18
  · rw [c64 19 (by decide) (by decide) (by decide), c43 19 (by decide) (by decide) (by decide),
      B3_orig 19 (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))]
    exact (Uniform.pad_blank Rc).symm
  · rw [B6off 20 (by decide) (Or.inr (by decide)) (Or.inr (by decide)) (by decide)]
    exact B5_20
  · rw [c64 21 (by decide) (by decide) (by decide), c43 21 (by decide) (by decide) (by decide)]
    exact B3_21
  · rw [c64 22 (by decide) (by decide) (by decide)]; exact B4_22
  · rw [c64 23 (by decide) (by decide) (by decide), c43 23 (by decide) (by decide) (by decide),
      B3_orig 23 (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))]
    exact (Uniform.pad_blank Rc).symm
  · rw [c64 24 (by decide) (by decide) (by decide), c43 24 (by decide) (by decide) (by decide),
      B3_orig 24 (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))]
    exact (Uniform.pad_blank Rc).symm
  · rw [c64 25 (by decide) (by decide) (by decide)]; exact B4_25
  · rw [c64 26 (by decide) (by decide) (by decide)]; exact B4_26
  · rw [c64 27 (by decide) (by decide) (by decide)]; exact B4_27
  · rw [c64 28 (by decide) (by decide) (by decide)]; exact B4_28
  · rw [c64 29 (by decide) (by decide) (by decide)]; exact B4_29
  · rw [c64 30 (by decide) (by decide) (by decide)]; exact B4_30
  · rw [c64 31 (by decide) (by decide) (by decide)]; exact B4_31
  · exact (install_slot un43 un43_inj B5 W6 0).trans h60
  · exact (install_slot un43 un43_inj B5 W6 1).trans h61
  · intro i hi
    exact L6 i (by simp only [E, not_lt]; exact hi)

end
end NearCubicWires.SourceConstruction.InitPost
end

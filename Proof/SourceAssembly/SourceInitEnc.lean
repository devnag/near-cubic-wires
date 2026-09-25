import Proof.SourceAssembly.SourceInitSlopes
import Proof.SourceAssembly.SourcePrologue

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
namespace NearCubicWires.SourceConstruction.InitEnc
noncomputable section

/-! ## 1. Three extra padded stages -/

/-- `ClockNormalize.scalar_run` at `bits = []`, padded by `Rc` (`1 ≤ Rc`): from `1^w` and blank tapes it
writes `frame (binary w 0)` on tape 2. -/
theorem stepZero (w Rc : ℕ) (hRc : 1 ≤ Rc) : Step ClockNormalize.machine (4*w+4) (fun _ => 0)
    ![ZeroPadding.pad Rc (List.replicate w true), ZeroPadding.pad Rc [], ZeroPadding.pad Rc [],
      ZeroPadding.pad Rc [], ZeroPadding.pad Rc []] (fun _ => 0)
    ![ZeroPadding.pad Rc (List.replicate w true), ZeroPadding.pad Rc [],
      ZeroPadding.pad Rc (frame (SignedSortKey.binary w 0)), ZeroPadding.pad Rc [true],
      ZeroPadding.pad Rc (List.replicate (2*w+1) false)] := by
  have h := (Prologue.scalar_step w [] (by simp)).pad (fun _ => Rc)
  have hf : ZeroPadding.pad Rc (frame []) = ZeroPadding.pad Rc [] := by
    obtain ⟨k, rfl⟩ : ∃ k, Rc = k + 1 := ⟨Rc - 1, by omega⟩
    simp [frame, ZeroPadding.pad, List.replicate_succ]
  refine (h.congr_in rfl ?_).congr rfl ?_
  · funext i; fin_cases i
    · rfl
    · exact hf
    · rfl
    · rfl
    · rfl
  · funext i; fin_cases i
    · rfl
    · exact hf
    · rfl
    · rfl
    · rfl

theorem stepApp (b Rc : ℕ) : ∃ W : Fin 42 → List Bool,
    Step CloseoutFinalC10AppendWorkspaceInit.machine (CloseoutFinalC10AppendWorkspaceInit.budget b) (fun _ => 0)
      (fun i => if i.val = 0 then List.replicate b true else ZeroPadding.pad Rc []) (fun _ => 0) W ∧
    W 0 = List.replicate b true ∧
    W 20 = ZeroPadding.pad Rc (UnaryTemplate.tape (20*b+22)) ∧
    W 39 = ZeroPadding.pad Rc (List.replicate (CloseoutFinalC10AppendWorkspaceInit.capacity b) false) ∧
    W 40 = ZeroPadding.pad Rc (List.replicate (CloseoutFinalC10AppendWorkspaceInit.capacity b) false) ∧
    (∀ j : Fin 42, j.val ≠ 0 → Rc ≤ (W j).length) := by
  obtain ⟨out, h, h0, h20, h39, h40⟩ := CloseoutFinalC10AppendWorkspaceInit.initialize_run b
  let cap : Fin 42 → ℕ := fun i => if i.val = 0 then 0 else Rc
  have hcap0 : cap 0 = 0 := rfl
  have hcap : ∀ j : Fin 42, j.val ≠ 0 → cap j = Rc := fun j hj => by
    show (if j.val = 0 then 0 else Rc) = Rc
    rw [if_neg hj]
  refine ⟨fun j => ZeroPadding.pad (cap j) (out j), (h.pad cap).congr_in rfl ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext i
    by_cases hi : i.val = 0
    · show ZeroPadding.pad (if i.val = 0 then 0 else Rc) (CloseoutFinalC10AppendWorkspaceInit.input b i) = _
      simp only [CloseoutFinalC10AppendWorkspaceInit.input, if_pos hi]
      exact ZeroPadding.pad_zero _
    · rw [hcap i hi]
      simp only [CloseoutFinalC10AppendWorkspaceInit.input, if_neg hi]
  · show ZeroPadding.pad (cap 0) (out 0) = _
    rw [hcap0, h0]; exact ZeroPadding.pad_zero _
  · show ZeroPadding.pad (cap 20) (out 20) = _
    rw [hcap 20 (by decide), h20]
  · show ZeroPadding.pad (cap 39) (out 39) = _
    rw [hcap 39 (by decide), h39]
  · show ZeroPadding.pad (cap 40) (out 40) = _
    rw [hcap 40 (by decide), h40]
  · intro j hj
    show Rc ≤ (ZeroPadding.pad (cap j) (out j)).length
    rw [hcap j hj]
    exact Uniform.long_pad Rc _

/-! ## 2. The local layout (119 tapes) -/

/-- A `poly_step 1 c` dock with its input on tape 0 and its private tapes from `base+1`. -/
def sp (base : ℕ) (h : base + 16 ≤ 119) : Fin (BlockPlatform.UnaryCalc.tapes 1) → Fin 119 :=
  fun j => ⟨if j.val = 0 then 0 else base + j.val, by
    have := j.isLt
    simp only [BlockPlatform.UnaryCalc.tapes, DimensionPolynomial.tapes] at this
    split_ifs <;> omega⟩

theorem sp_inj (base : ℕ) (h : base + 16 ≤ 119) (hb : 1 ≤ base) : Function.Injective (sp base h) := by
  intro a b hab
  have hv := congrArg Fin.val hab
  have ha := a.isLt; have hb' := b.isLt
  simp only [DimensionPolynomial.tapes] at ha hb'
  simp only [sp] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

def s1 := sp 0 (by decide)
def s2 : Fin 5 → Fin 119 := ![5, 16, 17, 18, 19]
def s3 := sp 19 (by decide)
def s4 : Fin 4 → Fin 119 := ![24, 35, 36, 37]
def s5 : Fin 4 → Fin 119 := ![24, 38, 39, 40]
def s6 : Fin 3 → Fin 119 := ![24, 41, 42]
def s7 : Fin 3 → Fin 119 := ![41, 43, 44]
def s8 := sp 44 (by decide)
def s9 : Fin (BlockPlatform.UnaryCalc.tapes 1) → Fin 119 := fun j => ⟨60 + j.val, by
  have := j.isLt
  simp only [BlockPlatform.UnaryCalc.tapes, DimensionPolynomial.tapes] at this
  omega⟩
def s10 : Fin 4 → Fin 119 := ![49, 65, 76, 77]
def s11 : Fin 42 → Fin 119 := fun j => ⟨if j.val = 0 then 0 else 77 + j.val, by
  have := j.isLt; split_ifs <;> omega⟩

theorem s1_inj : Function.Injective s1 := by
  intro a b hab
  have hv := congrArg Fin.val hab
  have ha := a.isLt; have hb' := b.isLt
  simp only [DimensionPolynomial.tapes] at ha hb'
  simp only [s1, sp] at hv
  apply Fin.ext
  split_ifs at hv <;> omega
theorem s2_inj : Function.Injective s2 := by decide
theorem s3_inj : Function.Injective s3 := sp_inj 19 _ (by decide)
theorem s4_inj : Function.Injective s4 := by decide
theorem s5_inj : Function.Injective s5 := by decide
theorem s6_inj : Function.Injective s6 := by decide
theorem s7_inj : Function.Injective s7 := by decide
theorem s8_inj : Function.Injective s8 := sp_inj 44 _ (by decide)
theorem s9_inj : Function.Injective s9 := by
  intro a b hab
  have hv := congrArg Fin.val hab
  simp only [s9] at hv
  exact Fin.ext (by omega)
theorem s10_inj : Function.Injective s10 := by decide
theorem s11_inj : Function.Injective s11 := by decide

theorem sp_val' (base : ℕ) (h : base + 16 ≤ 119) (j : Fin (BlockPlatform.UnaryCalc.tapes 1)) :
    (sp base h j).val = if j.val = 0 then 0 else base + j.val := rfl

theorem sp_lt (j : Fin (BlockPlatform.UnaryCalc.tapes 1)) : j.val < 16 := by
  have := j.isLt
  simp only [BlockPlatform.UnaryCalc.tapes, DimensionPolynomial.tapes] at this
  omega

/-- The input: `1^b` on tape 0, blank `pad Rc []` elsewhere. -/
def input (b Rc : ℕ) : Fin 119 → List Bool := fun i =>
  if i.val = 0 then List.replicate b true else ZeroPadding.pad Rc []

def machine :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine
    (RecoveryFocus.machine s1 (PCPSerializerCapacity.Power.machine 1 2))
    (RecoveryFocus.machine s2 ClockNormalize.machine))
    (RecoveryFocus.machine s3 (PCPSerializerCapacity.Power.machine 1 21)))
    (RecoveryFocus.machine s4 ClockUnarySum.machine))
    (RecoveryFocus.machine s5 ClockUnarySum.machine))
    (RecoveryFocus.machine s6 (DimensionTemplate.machine false)))
    (RecoveryFocus.machine s7 (UWalkUnary.machine false true)))
    (RecoveryFocus.machine s8 (PCPSerializerCapacity.Power.machine 1 40)))
    (RecoveryFocus.machine s9 (PCPSerializerCapacity.Power.machine 1 14)))
    (RecoveryFocus.machine s10 ClockUnarySum.machine))
    (RecoveryFocus.machine s11 CloseoutFinalC10AppendWorkspaceInit.machine)

/-- `r = 21(b+1)`. -/
abbrev rr (b : ℕ) : ℕ := 21*(b+1)

def cost (b : ℕ) : ℕ :=
  (((((((((PCPSerializerCapacity.Power.budget 1 2 b+1+(4*(2*(b+1))+4))+1+
    PCPSerializerCapacity.Power.budget 1 21 b)+1+(2*rr b+6))+1+(2*rr b+6))+1+(2*rr b+8))+1+
    (2*rr b+6))+1+PCPSerializerCapacity.Power.budget 1 40 b)+1+PCPSerializerCapacity.Power.budget 1 14 0)+1+
    (2*(40*(b+1)+14*(0+1))+6))+1+CloseoutFinalC10AppendWorkspaceInit.budget b

/-! ## 3. The run -/

theorem enc_run (b Rc : ℕ) (hRc : 1 ≤ Rc) : ∃ W : Fin 119 → List Bool,
    Step machine (cost b) (fun _ => 0) (input b Rc) (fun _ => 0) W ∧
    W 0 = List.replicate b true ∧
    W 17 = ZeroPadding.pad Rc (frame (SignedSortKey.binary (2*b+2) 0)) ∧
    W 40 = ZeroPadding.pad Rc (List.replicate (rr b+2) false) ∧
    W 43 = ZeroPadding.pad Rc (List.replicate (rr b+1) true) ∧
    W 37 = ZeroPadding.pad Rc (List.replicate (rr b+2) false) ∧
    W 77 = ZeroPadding.pad Rc (List.replicate (40*b+56) false) ∧
    W 116 = ZeroPadding.pad Rc (List.replicate (CloseoutFinalC10AppendWorkspaceInit.capacity b) false) ∧
    W 97 = ZeroPadding.pad Rc (UnaryTemplate.tape (20*b+22)) ∧
    W 117 = ZeroPadding.pad Rc (List.replicate (CloseoutFinalC10AppendWorkspaceInit.capacity b) false) ∧
    (∀ i : Fin 119, i.val ≠ 0 → Rc ≤ (W i).length) := by
  let E : Fin 119 → Prop := fun i => i.val = 0
  let B0 := input b Rc
  have L0 : ∀ i, ¬ E i → Rc ≤ (B0 i).length := by
    intro i hi
    simp only [E] at hi
    simp only [B0, input, if_neg hi]
    exact Uniform.long_pad Rc _
  have bl0 : ∀ i : Fin 119, 1 ≤ i.val → B0 i = ZeroPadding.pad Rc [] := by
    intro i hi
    simp only [B0, input, if_neg (show i.val ≠ 0 by omega)]
  have B0_0 : B0 0 = List.replicate b true := by simp [B0, input]
  -- E1: 1^(2(b+1)) on tape 5
  obtain ⟨W1, h1s, h10, h15, h1l⟩ := Uniform.stepP 2 b Rc
  have st1 := Dimension.dock0 h1s s1 s1_inj B0 (by
    intro j
    by_cases hj : j.val = 0
    · have e : s1 j = 0 := Fin.ext (by simp [s1, sp, hj])
      rw [e, if_pos hj]; exact B0_0
    · have hv : (s1 j).val = 0 + j.val := by rw [show s1 = sp 0 (by decide) from rfl, sp_val', if_neg hj]
      rw [if_neg hj, Uniform.pad_blank]
      exact bl0 _ (by omega))
  let B1 := install s1 B0 W1
  have L1 := RowConst.long_install s1 s1_inj B0 W1 E Rc L0 (by
    intro j hj
    by_cases h0 : j.val = 0
    · exact absurd (by simp [E, s1, sp, h0]) hj
    · exact h1l j h0)
  have B1off : ∀ i : Fin 119, 16 ≤ i.val → B1 i = B0 i := by
    intro i hi
    refine install_other s1 B0 W1 i (fun j hj => ?_)
    have h1 := congrArg Fin.val hj
    have h2 := sp_lt j
    rw [show s1 = sp 0 (by decide) from rfl, sp_val'] at h1
    split_ifs at h1 <;> omega
  have B1_0 : B1 0 = List.replicate b true := (install_slot s1 s1_inj B0 W1 ⟨0, by decide⟩).trans h10
  have B1_5 : B1 5 = ZeroPadding.pad Rc (List.replicate (2*(b+1)) true) :=
    (install_slot s1 s1_inj B0 W1 ⟨5, by decide⟩).trans h15
  have B1blank : ∀ i : Fin 119, 16 ≤ i.val → B1 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B1off i hi).trans (bl0 i (by omega))
  -- E2: frame (binary (2(b+1)) 0) on tape 17
  let o2 : Fin 5 → List Bool := ![ZeroPadding.pad Rc (List.replicate (2*(b+1)) true), ZeroPadding.pad Rc [],
      ZeroPadding.pad Rc (frame (SignedSortKey.binary (2*(b+1)) 0)), ZeroPadding.pad Rc [true],
      ZeroPadding.pad Rc (List.replicate (2*(2*(b+1))+1) false)]
  have st2 := Dimension.dock0 (stepZero (2*(b+1)) Rc hRc) s2 s2_inj B1 (by
    intro j
    fin_cases j
    · exact B1_5
    · exact B1blank 16 (by decide)
    · exact B1blank 17 (by decide)
    · exact B1blank 18 (by decide)
    · exact B1blank 19 (by decide))
  let B2 := install s2 B1 o2
  have L2 := RowConst.long_install s2 s2_inj B1 o2 E Rc L1 (by
    intro j _
    fin_cases j <;> exact Uniform.long_pad Rc _)
  have B2off : ∀ i : Fin 119, i.val ≠ 5 → i.val ≠ 16 → i.val ≠ 17 → i.val ≠ 18 → i.val ≠ 19 → B2 i = B1 i := by
    intro i h1 h2 h3 h4 h5
    refine install_other s2 B1 o2 i (fun k hk => ?_)
    have := congrArg Fin.val hk
    fin_cases k <;> simp [s2] at this <;> omega
  have B2_17 : B2 17 = ZeroPadding.pad Rc (frame (SignedSortKey.binary (2*(b+1)) 0)) :=
    install_slot s2 s2_inj B1 o2 2
  have B2blank : ∀ i : Fin 119, 20 ≤ i.val → B2 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B2off i (by omega) (by omega) (by omega) (by omega) (by omega)).trans (B1blank i (by omega))
  have B2_0 : B2 0 = List.replicate b true :=
    (B2off 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans B1_0
  -- E3: 1^r on tape 24
  obtain ⟨W3, h3s, h30, h35, h3l⟩ := Uniform.stepP 21 b Rc
  have st3 := Dimension.dock0 h3s s3 s3_inj B2 (by
    intro j
    by_cases hj : j.val = 0
    · have e : s3 j = 0 := Fin.ext (by simp [s3, sp, hj])
      rw [e, if_pos hj]; exact B2_0
    · have hv : (s3 j).val = 19 + j.val := by rw [show s3 = sp 19 (by decide) from rfl, sp_val', if_neg hj]
      rw [if_neg hj, Uniform.pad_blank]
      exact B2blank _ (by omega))
  let B3 := install s3 B2 W3
  have L3 := RowConst.long_install s3 s3_inj B2 W3 E Rc L2 (by
    intro j hj
    by_cases h0 : j.val = 0
    · exact absurd (by simp [E, s3, sp, h0]) hj
    · exact h3l j h0)
  have B3off : ∀ i : Fin 119, (35 ≤ i.val ∨ (1 ≤ i.val ∧ i.val ≤ 19)) → B3 i = B2 i := by
    intro i hi
    refine install_other s3 B2 W3 i (fun j hj => ?_)
    have h1 := congrArg Fin.val hj
    have h2 := sp_lt j
    rw [show s3 = sp 19 (by decide) from rfl, sp_val'] at h1
    split_ifs at h1 <;> omega
  have B3_0 : B3 0 = List.replicate b true := (install_slot s3 s3_inj B2 W3 ⟨0, by decide⟩).trans h30
  have B3_24 : B3 24 = ZeroPadding.pad Rc (List.replicate (rr b) true) :=
    (install_slot s3 s3_inj B2 W3 ⟨5, by decide⟩).trans h35
  have B3blank : ∀ i : Fin 119, 35 ≤ i.val → B3 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B3off i (Or.inl hi)).trans (B2blank i (by omega))
  have B3_17 : B3 17 = ZeroPadding.pad Rc (frame (SignedSortKey.binary (2*(b+1)) 0)) :=
    (B3off 17 (Or.inr (by decide))).trans B2_17
  -- E4: 0^(r+2) on tape 37
  let o4 : Fin 4 → List Bool := ![ZeroPadding.pad Rc (List.replicate (rr b) true), ZeroPadding.pad Rc [],
    ZeroPadding.pad Rc (List.replicate (rr b) true), ZeroPadding.pad Rc (List.replicate (rr b+2) false)]
  have st4 := Dimension.dock0 (RowConst.stepCopy (rr b) Rc) s4 s4_inj B3 (by
    intro j
    fin_cases j
    · exact B3_24
    · exact B3blank 35 (by decide)
    · exact B3blank 36 (by decide)
    · exact B3blank 37 (by decide))
  let B4 := install s4 B3 o4
  have L4 := RowConst.long_install s4 s4_inj B3 o4 E Rc L3 (by
    intro j _
    fin_cases j <;> exact Uniform.long_pad Rc _)
  have B4off : ∀ i : Fin 119, i.val ≠ 24 → i.val ≠ 35 → i.val ≠ 36 → i.val ≠ 37 → B4 i = B3 i := by
    intro i h1 h2 h3 h4
    refine install_other s4 B3 o4 i (fun k hk => ?_)
    have := congrArg Fin.val hk
    fin_cases k <;> simp [s4] at this <;> omega
  have B4_24 : B4 24 = ZeroPadding.pad Rc (List.replicate (rr b) true) := install_slot s4 s4_inj B3 o4 0
  have B4_37 : B4 37 = ZeroPadding.pad Rc (List.replicate (rr b+2) false) := install_slot s4 s4_inj B3 o4 3
  have B4blank : ∀ i : Fin 119, 38 ≤ i.val → B4 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B4off i (by omega) (by omega) (by omega) (by omega)).trans (B3blank i (by omega))
  -- E5: 0^(r+2) on tape 40
  let o5 : Fin 4 → List Bool := ![ZeroPadding.pad Rc (List.replicate (rr b) true), ZeroPadding.pad Rc [],
    ZeroPadding.pad Rc (List.replicate (rr b) true), ZeroPadding.pad Rc (List.replicate (rr b+2) false)]
  have st5 := Dimension.dock0 (RowConst.stepCopy (rr b) Rc) s5 s5_inj B4 (by
    intro j
    fin_cases j
    · exact B4_24
    · exact B4blank 38 (by decide)
    · exact B4blank 39 (by decide)
    · exact B4blank 40 (by decide))
  let B5 := install s5 B4 o5
  have L5 := RowConst.long_install s5 s5_inj B4 o5 E Rc L4 (by
    intro j _
    fin_cases j <;> exact Uniform.long_pad Rc _)
  have B5off : ∀ i : Fin 119, i.val ≠ 24 → i.val ≠ 38 → i.val ≠ 39 → i.val ≠ 40 → B5 i = B4 i := by
    intro i h1 h2 h3 h4
    refine install_other s5 B4 o5 i (fun k hk => ?_)
    have := congrArg Fin.val hk
    fin_cases k <;> simp [s5] at this <;> omega
  have B5_24 : B5 24 = ZeroPadding.pad Rc (List.replicate (rr b) true) := install_slot s5 s5_inj B4 o5 0
  have B5_40 : B5 40 = ZeroPadding.pad Rc (List.replicate (rr b+2) false) := install_slot s5 s5_inj B4 o5 3
  have B5blank : ∀ i : Fin 119, 41 ≤ i.val → B5 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B5off i (by omega) (by omega) (by omega) (by omega)).trans (B4blank i (by omega))
  -- E6: tape r on tape 41
  let o6 : Fin 3 → List Bool := ![ZeroPadding.pad Rc (List.replicate (rr b) true),
    ZeroPadding.pad Rc (UnaryTemplate.tape (rr b + false.toNat)),
    ZeroPadding.pad Rc (List.replicate (rr b+3) false)]
  have st6 := Dimension.dock0 (Uniform.stepT false (rr b) Rc Rc Rc) s6 s6_inj B5 (by
    intro j
    fin_cases j
    · exact B5_24
    · exact B5blank 41 (by decide)
    · exact B5blank 42 (by decide))
  let B6 := install s6 B5 o6
  have L6 := RowConst.long_install s6 s6_inj B5 o6 E Rc L5 (by
    intro j _
    fin_cases j <;> exact Uniform.long_pad Rc _)
  have B6off : ∀ i : Fin 119, i.val ≠ 24 → i.val ≠ 41 → i.val ≠ 42 → B6 i = B5 i := by
    intro i h1 h2 h3
    refine install_other s6 B5 o6 i (fun k hk => ?_)
    have := congrArg Fin.val hk
    fin_cases k <;> simp [s6] at this <;> omega
  have B6_41 : B6 41 = ZeroPadding.pad Rc (UnaryTemplate.tape (rr b)) :=
    (install_slot s6 s6_inj B5 o6 1).trans (by simp only [o6, Bool.toNat_false, Nat.add_zero]; rfl)
  have B6blank : ∀ i : Fin 119, 43 ≤ i.val → B6 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B6off i (by omega) (by omega) (by omega)).trans (B5blank i (by omega))
  -- E7: 1^(r+1) on tape 43
  let o7 : Fin 3 → List Bool := ![ZeroPadding.pad Rc (UnaryTemplate.tape (rr b)),
    ZeroPadding.pad Rc (UWalkUnary.output false true (rr b)), ZeroPadding.pad Rc (List.replicate (rr b+2) false)]
  have st7 := Dimension.dock0 (RowConst.stepUW false true (rr b) Rc Rc Rc) s7 s7_inj B6 (by
    intro j
    fin_cases j
    · exact B6_41
    · exact B6blank 43 (by decide)
    · exact B6blank 44 (by decide))
  let B7 := install s7 B6 o7
  have L7 := RowConst.long_install s7 s7_inj B6 o7 E Rc L6 (by
    intro j _
    fin_cases j <;> exact Uniform.long_pad Rc _)
  have B7off : ∀ i : Fin 119, i.val ≠ 41 → i.val ≠ 43 → i.val ≠ 44 → B7 i = B6 i := by
    intro i h1 h2 h3
    refine install_other s7 B6 o7 i (fun k hk => ?_)
    have := congrArg Fin.val hk
    fin_cases k <;> simp [s7] at this <;> omega
  have B7_43 : B7 43 = ZeroPadding.pad Rc (List.replicate (rr b+1) true) :=
    (install_slot s7 s7_inj B6 o7 1).trans (by simp only [o7]; rw [RowConst.out_ft]; rfl)
  have B7blank : ∀ i : Fin 119, 45 ≤ i.val → B7 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B7off i (by omega) (by omega) (by omega)).trans (B6blank i (by omega))
  have B7_0 : B7 0 = List.replicate b true :=
    (B7off 0 (by decide) (by decide) (by decide)).trans ((B6off 0 (by decide) (by decide) (by decide)).trans
      ((B5off 0 (by decide) (by decide) (by decide) (by decide)).trans
        ((B4off 0 (by decide) (by decide) (by decide) (by decide)).trans B3_0)))
  -- E8: 1^(40(b+1)) on tape 49
  obtain ⟨W8, h8s, h80, h85, h8l⟩ := Uniform.stepP 40 b Rc
  have st8 := Dimension.dock0 h8s s8 s8_inj B7 (by
    intro j
    by_cases hj : j.val = 0
    · have e : s8 j = 0 := Fin.ext (by simp [s8, sp, hj])
      rw [e, if_pos hj]; exact B7_0
    · have hv : (s8 j).val = 44 + j.val := by rw [show s8 = sp 44 (by decide) from rfl, sp_val', if_neg hj]
      rw [if_neg hj, Uniform.pad_blank]
      exact B7blank _ (by omega))
  let B8 := install s8 B7 W8
  have L8 := RowConst.long_install s8 s8_inj B7 W8 E Rc L7 (by
    intro j hj
    by_cases h0 : j.val = 0
    · exact absurd (by simp [E, s8, sp, h0]) hj
    · exact h8l j h0)
  have B8off : ∀ i : Fin 119, (60 ≤ i.val ∨ (1 ≤ i.val ∧ i.val ≤ 44)) → B8 i = B7 i := by
    intro i hi
    refine install_other s8 B7 W8 i (fun j hj => ?_)
    have h1 := congrArg Fin.val hj
    have h2 := sp_lt j
    rw [show s8 = sp 44 (by decide) from rfl, sp_val'] at h1
    split_ifs at h1 <;> omega
  have B8_0 : B8 0 = List.replicate b true := (install_slot s8 s8_inj B7 W8 ⟨0, by decide⟩).trans h80
  have B8_49 : B8 49 = ZeroPadding.pad Rc (List.replicate (40*(b+1)) true) :=
    (install_slot s8 s8_inj B7 W8 ⟨5, by decide⟩).trans h85
  have B8blank : ∀ i : Fin 119, 60 ≤ i.val → B8 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B8off i (Or.inl hi)).trans (B7blank i (by omega))
  -- E9: 1^14 on tape 65
  obtain ⟨W9, h9s, _, h95, h9l⟩ := RowConst.stepPoly 14 0 Rc
  have st9 := Dimension.dock0 h9s s9 s9_inj B8 (by
    intro j
    have hj := j.isLt
    simp only [DimensionPolynomial.tapes] at hj
    rw [B8blank _ (by simp only [s9]; omega)]
    split_ifs <;> rfl)
  let B9 := install s9 B8 W9
  have L9 := RowConst.long_install s9 s9_inj B8 W9 E Rc L8 (fun j _ => h9l j)
  have B9off : ∀ i : Fin 119, (i.val < 60 ∨ 76 ≤ i.val) → B9 i = B8 i := by
    intro i hi
    refine install_other s9 B8 W9 i (fun j hj => ?_)
    have h1 := congrArg Fin.val hj
    have hj := j.isLt
    simp only [BlockPlatform.UnaryCalc.tapes, DimensionPolynomial.tapes] at hj
    simp only [s9] at h1
    omega
  have B9_65 : B9 65 = ZeroPadding.pad Rc (List.replicate (14*(0+1)) true) :=
    (install_slot s9 s9_inj B8 W9 ⟨5, by decide⟩).trans h95
  have B9blank : ∀ i : Fin 119, 76 ≤ i.val → B9 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B9off i (Or.inr hi)).trans (B8blank i (by omega))
  have B9_49 : B9 49 = ZeroPadding.pad Rc (List.replicate (40*(b+1)) true) :=
    (B9off 49 (Or.inl (by decide))).trans B8_49
  -- E10: 0^(40b+56) on tape 77
  let o10 : Fin 4 → List Bool := ![ZeroPadding.pad Rc (List.replicate (40*(b+1)) true),
    ZeroPadding.pad Rc (List.replicate (14*(0+1)) true),
    ZeroPadding.pad Rc (List.replicate (40*(b+1)+14*(0+1)) true),
    ZeroPadding.pad Rc (List.replicate (40*(b+1)+14*(0+1)+2) false)]
  have st10 := Dimension.dock0 (RowWidth.stepSp (40*(b+1)) (14*(0+1)) Rc) s10 s10_inj B9 (by
    intro j
    fin_cases j
    · exact B9_49
    · exact B9_65
    · exact B9blank 76 (by decide)
    · exact B9blank 77 (by decide))
  let B10 := install s10 B9 o10
  have L10 := RowConst.long_install s10 s10_inj B9 o10 E Rc L9 (by
    intro j _
    fin_cases j <;> exact Uniform.long_pad Rc _)
  have B10off : ∀ i : Fin 119, i.val ≠ 49 → i.val ≠ 65 → i.val ≠ 76 → i.val ≠ 77 → B10 i = B9 i := by
    intro i h1 h2 h3 h4
    refine install_other s10 B9 o10 i (fun k hk => ?_)
    have := congrArg Fin.val hk
    fin_cases k <;> simp [s10] at this <;> omega
  have e56 : 40*(b+1)+14*(0+1)+2 = 40*b+56 := by omega
  have B10_77 : B10 77 = ZeroPadding.pad Rc (List.replicate (40*b+56) false) :=
    (install_slot s10 s10_inj B9 o10 3).trans (by simp only [o10]; rw [e56]; rfl)
  have B10blank : ∀ i : Fin 119, 78 ≤ i.val → B10 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B10off i (by omega) (by omega) (by omega) (by omega)).trans (B9blank i (by omega))
  have B10_0 : B10 0 = List.replicate b true :=
    (B10off 0 (by decide) (by decide) (by decide) (by decide)).trans
      ((B9off 0 (Or.inl (by decide))).trans B8_0)
  -- E11: the append workspace constants
  obtain ⟨W11, h11s, h110, h1120, h1139, h1140, h11l⟩ := stepApp b Rc
  have st11 := Dimension.dock0 h11s s11 s11_inj B10 (by
    intro j
    by_cases hj : j.val = 0
    · have e : s11 j = 0 := Fin.ext (by simp [s11, hj])
      rw [e, if_pos hj]; exact B10_0
    · have hj' := j.isLt
      rw [if_neg hj]
      exact B10blank _ (by simp only [s11, hj, if_false]; omega))
  let B11 := install s11 B10 W11
  have L11 := RowConst.long_install s11 s11_inj B10 W11 E Rc L10 (by
    intro j hj
    by_cases h0 : j.val = 0
    · exact absurd (by simp [E, s11, h0]) hj
    · exact h11l j h0)
  have B11off : ∀ i : Fin 119, 1 ≤ i.val → i.val ≤ 77 → B11 i = B10 i := by
    intro i h1 h2
    refine install_other s11 B10 W11 i (fun j hj => ?_)
    have hv := congrArg Fin.val hj
    have := j.isLt
    simp only [s11] at hv
    split_ifs at hv <;> omega
  -- the tapes written before E11, carried through E10 and E11
  have c10 : ∀ i : Fin 119, 1 ≤ i.val → i.val ≤ 44 → B11 i = B7 i := by
    intro i h1 h2
    rw [B11off i h1 (by omega), B10off i (by omega) (by omega) (by omega) (by omega),
      B9off i (Or.inl (by omega)), B8off i (Or.inr ⟨h1, h2⟩)]
  refine ⟨B11, (((((((((st1.seq st2).seq st3).seq st4).seq st5).seq st6).seq st7).seq st8).seq st9).seq
    st10).seq st11, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (install_slot s11 s11_inj B10 W11 ⟨0, by decide⟩).trans h110
  · rw [show 2*b+2 = 2*(b+1) by ring, c10 17 (by decide) (by decide), B7off 17 (by decide) (by decide) (by decide),
      B6off 17 (by decide) (by decide) (by decide), B5off 17 (by decide) (by decide) (by decide) (by decide),
      B4off 17 (by decide) (by decide) (by decide) (by decide)]
    exact B3_17
  · rw [c10 40 (by decide) (by decide), B7off 40 (by decide) (by decide) (by decide),
      B6off 40 (by decide) (by decide) (by decide)]
    exact B5_40
  · rw [c10 43 (by decide) (by decide)]
    exact B7_43
  · rw [c10 37 (by decide) (by decide), B7off 37 (by decide) (by decide) (by decide),
      B6off 37 (by decide) (by decide) (by decide), B5off 37 (by decide) (by decide) (by decide) (by decide)]
    exact B4_37
  · rw [B11off 77 (by decide) (by decide)]
    exact B10_77
  · exact (install_slot s11 s11_inj B10 W11 39).trans h1139
  · exact (install_slot s11 s11_inj B10 W11 20).trans h1120
  · exact (install_slot s11 s11_inj B10 W11 40).trans h1140
  · intro i hi
    exact L11 i hi

end
end NearCubicWires.SourceConstruction.InitEnc
end

import Proof.SourceAssembly.SourceRestLayout

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open NearCubicWires.SupplierEstimator
namespace NearCubicWires.SourceConstruction.InitSlopes
noncomputable section

/-! ## 1. Two extra padded stages -/

theorem stepDiv (n d Rc : ℕ) (hd : 0 < d) : ∃ W : Fin 4 → List Bool,
    Step MatrixBucketDivide.machine (8*n+6) (fun _ => 0)
      ![ZeroPadding.pad Rc (List.replicate n true), ZeroPadding.pad Rc (UnaryTemplate.tape d),
        ZeroPadding.pad Rc [], ZeroPadding.pad Rc []] (fun _ => 0) W ∧
    W 0 = ZeroPadding.pad Rc (List.replicate n true) ∧
    W 1 = ZeroPadding.pad Rc (UnaryTemplate.tape d) ∧
    W 2 = ZeroPadding.pad Rc (List.replicate (n/d) true) ∧
    (∀ j, Rc ≤ (W j).length) := by
  obtain ⟨r, hr, h0, h1, h2, hh, hs⟩ := MatrixBucketDivide.divide_run n d hd
  have hst : Step MatrixBucketDivide.machine (8*n+6) (fun _ => 0) (MatrixBucketDivide.resetInput n d)
      (fun _ => 0) r.final.tapes := by
    refine ⟨r, ?_, funext hh, rfl, hs⟩
    change runFrom _ _ (initialConfiguration _ _) = some r at hr
    exact hr
  refine ⟨fun j => ZeroPadding.pad Rc (r.final.tapes j), (hst.pad (fun _ => Rc)).congr_in rfl ?_,
    ?_, ?_, ?_, ?_⟩
  · funext i; fin_cases i <;> rfl
  · show ZeroPadding.pad Rc (r.final.tapes 0) = _; rw [h0]
  · show ZeroPadding.pad Rc (r.final.tapes 1) = _; rw [h1]
  · show ZeroPadding.pad Rc (r.final.tapes 2) = _; rw [h2]
  · intro j; exact Uniform.long_pad Rc _

/-- The product, padded by `Rc` on all four tapes, with the second factor a template. -/
theorem stepProd (d e Rc : ℕ) : Step ClockUnaryProduct.machine (2*(d*(2*e+3)+2)+2) (fun _ => 0)
    ![ZeroPadding.pad Rc (List.replicate d true), ZeroPadding.pad Rc (UnaryTemplate.tape e),
      ZeroPadding.pad Rc [], ZeroPadding.pad Rc []] (fun _ => 0)
    ![ZeroPadding.pad Rc (List.replicate d true), ZeroPadding.pad Rc (UnaryTemplate.tape e),
      ZeroPadding.pad Rc (List.replicate (d*e) true),
      ZeroPadding.pad Rc (List.replicate (d*(2*e+3)+2) false)] := by
  have h := (Dimension.stepH d e).pad (fun _ => Rc)
  refine (h.congr_in rfl ?_).congr rfl ?_
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-! ## 2. The local layout (57 tapes) -/

def sa : Fin 3 → Fin 57 := ![0, 2, 3]
def sb : Fin 27 → Fin 57 := fun j => ⟨if j.val = 0 then 2 else 3 + j.val, by
  have := j.isLt; split_ifs <;> omega⟩
def sc : Fin 3 → Fin 57 := ![28, 30, 31]
def sd : Fin (BlockPlatform.UnaryCalc.tapes 1) → Fin 57 := fun j => ⟨if j.val = 0 then 30 else 31 + j.val, by
  have := j.isLt
  simp only [BlockPlatform.UnaryCalc.tapes, DimensionPolynomial.tapes] at this
  split_ifs <;> omega⟩
def se : Fin 3 → Fin 57 := ![36, 47, 48]
def sf : Fin 3 → Fin 57 := ![0, 49, 50]
def sg : Fin 4 → Fin 57 := ![49, 47, 51, 52]
def sh : Fin 3 → Fin 57 := ![1, 53, 54]
def si : Fin 4 → Fin 57 := ![51, 53, 55, 56]

theorem sa_inj : Function.Injective sa := by decide
theorem sb_inj : Function.Injective sb := by decide
theorem sc_inj : Function.Injective sc := by decide
theorem sd_inj : Function.Injective sd := by
  intro a b h
  have hv := congrArg Fin.val h
  have ha := a.isLt; have hb := b.isLt
  simp only [BlockPlatform.UnaryCalc.tapes, DimensionPolynomial.tapes] at ha hb
  simp only [sd] at hv
  apply Fin.ext
  split_ifs at hv <;> omega
theorem se_inj : Function.Injective se := by decide
theorem sf_inj : Function.Injective sf := by decide
theorem sg_inj : Function.Injective sg := by decide
theorem sh_inj : Function.Injective sh := by decide
theorem si_inj : Function.Injective si := by decide

/-- The input: the arity template on tape 0, `pad Rc (1^Ms)` on tape 1, blank `pad Rc []` elsewhere. -/
def input (q Ms Rc : ℕ) : Fin 57 → List Bool := fun i =>
  if i.val = 0 then UnaryTemplate.tape q
  else if i.val = 1 then ZeroPadding.pad Rc (List.replicate Ms true)
  else ZeroPadding.pad Rc []

/-- The divisor `200(K+2)`. -/
abbrev dv (L q : ℕ) : ℕ := 200*(normalizedLiveCount q L+1+1)

def machine (L : ℕ) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine sa (UWalkUnary.machine true false))
    (RecoveryFocus.machine sb (PCJ6e421fabe2aa4155_SourceLiveCount.machine L)))
    (RecoveryFocus.machine sc (UWalkUnary.machine false true)))
    (RecoveryFocus.machine sd (PCPSerializerCapacity.Power.machine 1 200)))
    (RecoveryFocus.machine se (DimensionTemplate.machine false)))
    (RecoveryFocus.machine sf (UWalkUnary.machine false false)))
    (RecoveryFocus.machine sg MatrixBucketDivide.machine))
    (RecoveryFocus.machine sh (DimensionTemplate.machine false)))
    (RecoveryFocus.machine si ClockUnaryProduct.machine)

def cost (L q Ms : ℕ) : ℕ :=
  let K := normalizedLiveCount q L
  ((((((((2*q+6)+1+PCJ6e421fabe2aa4155_SourceLiveCount.budget q L)+1+(2*K+6))+1+
    PCPSerializerCapacity.Power.budget 1 200 (K+1))+1+(2*dv L q+8))+1+(2*q+6))+1+(8*q+6))+1+
    (2*Ms+8))+1+(2*(q/dv L q*(2*Ms+3)+2)+2)

/-! ## 3. The run -/

theorem slopes_run (L q Ms Rc : ℕ) : ∃ W : Fin 57 → List Bool,
    Step (machine L) (cost L q Ms) (fun _ => 0) (input q Ms Rc) (fun _ => 0) W ∧
    W 0 = UnaryTemplate.tape q ∧
    W 1 = ZeroPadding.pad Rc (List.replicate Ms true) ∧
    W 49 = ZeroPadding.pad Rc (List.replicate q true) ∧
    W 55 = ZeroPadding.pad Rc (List.replicate (q / dv L q * Ms) true) ∧
    (∀ i : Fin 57, i.val ≠ 0 → Rc ≤ (W i).length) := by
  let K := normalizedLiveCount q L
  let E : Fin 57 → Prop := fun i => i.val = 0
  let B0 := input q Ms Rc
  have L0 : ∀ i, ¬ E i → Rc ≤ (B0 i).length := by
    intro i hi
    simp only [E] at hi
    simp only [B0, input, if_neg hi]
    split_ifs <;> exact Uniform.long_pad Rc _
  have bl0 : ∀ i : Fin 57, 2 ≤ i.val → B0 i = ZeroPadding.pad Rc [] := by
    intro i hi
    simp only [B0, input, if_neg (show i.val ≠ 0 by omega), if_neg (show i.val ≠ 1 by omega)]
  -- a: word q
  let oA : Fin 3 → List Bool := ![ZeroPadding.pad 0 (UnaryTemplate.tape q),
    ZeroPadding.pad Rc (UWalkUnary.output true false q), ZeroPadding.pad Rc (List.replicate (q+2) false)]
  have s1 := Dimension.dock0 (RowConst.stepUW true false q 0 Rc Rc) sa sa_inj B0 (by
    intro j
    fin_cases j
    · exact (ZeroPadding.pad_zero _).symm
    · exact bl0 2 (by decide)
    · exact bl0 3 (by decide))
  let B1 := install sa B0 oA
  have L1 := RowConst.long_install sa sa_inj B0 oA E Rc L0 (by
    intro j hj
    fin_cases j
    · exact absurd rfl hj
    all_goals exact Uniform.long_pad Rc _)
  have B1off : ∀ i : Fin 57, i.val ≠ 0 → i.val ≠ 2 → i.val ≠ 3 → B1 i = B0 i := by
    intro i h1 h2 h3
    refine install_other sa B0 oA i (fun k hk => ?_)
    have := congrArg Fin.val hk
    fin_cases k <;> simp [sa] at this <;> omega
  have B1_0 : B1 0 = UnaryTemplate.tape q :=
    (install_slot sa sa_inj B0 oA 0).trans (ZeroPadding.pad_zero _)
  have B1_2 : B1 2 = ZeroPadding.pad Rc (CompareMachine.word q) :=
    (install_slot sa sa_inj B0 oA 1).trans (by simp only [oA]; rw [RowConst.out_tf]; rfl)
  have B1blank : ∀ i : Fin 57, 4 ≤ i.val → B1 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B1off i (by omega) (by omega) (by omega)).trans (bl0 i (by omega))
  have B1_1 : B1 1 = ZeroPadding.pad Rc (List.replicate Ms true) :=
    (B1off 1 (by decide) (by decide) (by decide)).trans (by simp [B0, input])
  -- b: tape K
  obtain ⟨WB, hBs, hB25, hBl⟩ := RowConst.stepLC q L Rc
  have s2 := Dimension.dock0 hBs sb sb_inj B1 (by
    intro j
    by_cases hj : j.val = 0
    · have e : sb j = 2 := Fin.ext (by simp [sb, hj])
      rw [e, if_pos hj]
      exact B1_2
    · have hj' := j.isLt
      have hv : (sb j).val = 3 + j.val := by simp [sb, hj]
      rw [if_neg hj]
      exact B1blank _ (by omega))
  let B2 := install sb B1 WB
  have L2 := RowConst.long_install sb sb_inj B1 WB E Rc L1 (fun j _ => hBl j)
  have sb_lt : ∀ j, (sb j).val < 30 := by
    intro j; have := j.isLt; simp only [sb]; split_ifs <;> omega
  have B2off : ∀ i : Fin 57, (30 ≤ i.val ∨ i.val < 2) → B2 i = B1 i := by
    intro i hi
    refine install_other sb B1 WB i (fun j hj => ?_)
    have h1 := congrArg Fin.val hj
    have h2 := sb_lt j
    have h3 : 2 ≤ (sb j).val := by simp only [sb]; split_ifs <;> omega
    omega
  have B2_28 : B2 28 = ZeroPadding.pad Rc (UnaryTemplate.tape K) :=
    (install_slot sb sb_inj B1 WB 25).trans hB25
  have B2blank : ∀ i : Fin 57, 30 ≤ i.val → B2 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B2off i (Or.inl hi)).trans (B1blank i (by omega))
  have B2_0 : B2 0 = UnaryTemplate.tape q := (B2off 0 (Or.inr (by decide))).trans B1_0
  have B2_1 : B2 1 = ZeroPadding.pad Rc (List.replicate Ms true) := (B2off 1 (Or.inr (by decide))).trans B1_1
  -- c: 1^(K+1)
  let oC : Fin 3 → List Bool := ![ZeroPadding.pad Rc (UnaryTemplate.tape K),
    ZeroPadding.pad Rc (UWalkUnary.output false true K), ZeroPadding.pad Rc (List.replicate (K+2) false)]
  have s3 := Dimension.dock0 (RowConst.stepUW false true K Rc Rc Rc) sc sc_inj B2 (by
    intro j
    fin_cases j
    · exact B2_28
    · exact B2blank 30 (by decide)
    · exact B2blank 31 (by decide))
  let B3 := install sc B2 oC
  have L3 := RowConst.long_install sc sc_inj B2 oC E Rc L2 (by
    intro j _
    fin_cases j <;> exact Uniform.long_pad Rc _)
  have B3off : ∀ i : Fin 57, i.val ≠ 28 → i.val ≠ 30 → i.val ≠ 31 → B3 i = B2 i := by
    intro i h1 h2 h3
    refine install_other sc B2 oC i (fun k hk => ?_)
    have := congrArg Fin.val hk
    fin_cases k <;> simp [sc] at this <;> omega
  have B3_30 : B3 30 = ZeroPadding.pad Rc (List.replicate (K+1) true) :=
    (install_slot sc sc_inj B2 oC 1).trans (by simp only [oC]; rw [RowConst.out_ft]; rfl)
  have B3blank : ∀ i : Fin 57, 32 ≤ i.val → B3 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B3off i (by omega) (by omega) (by omega)).trans (B2blank i (by omega))
  have B3_0 : B3 0 = UnaryTemplate.tape q := (B3off 0 (by decide) (by decide) (by decide)).trans B2_0
  have B3_1 : B3 1 = ZeroPadding.pad Rc (List.replicate Ms true) :=
    (B3off 1 (by decide) (by decide) (by decide)).trans B2_1
  -- d: 1^(200(K+2))
  obtain ⟨WD, hDs, hD0, hD5, hDl⟩ := RowConst.stepPoly 200 (K+1) Rc
  have s4 := Dimension.dock0 hDs sd sd_inj B3 (by
    intro j
    by_cases hj : j.val = 0
    · have e : sd j = 30 := Fin.ext (by simp [sd, hj])
      rw [e, if_pos hj]
      exact B3_30
    · have hj' := j.isLt
      simp only [DimensionPolynomial.tapes] at hj'
      have hv : (sd j).val = 31 + j.val := by simp [sd, hj]
      rw [if_neg hj]
      exact B3blank _ (by omega))
  let B4 := install sd B3 WD
  have L4 := RowConst.long_install sd sd_inj B3 WD E Rc L3 (fun j _ => hDl j)
  have sd_lt : ∀ j, (sd j).val < 47 := by
    intro j; have := j.isLt
    simp only [BlockPlatform.UnaryCalc.tapes, DimensionPolynomial.tapes] at this
    simp only [sd]; split_ifs <;> omega
  have B4off : ∀ i : Fin 57, (47 ≤ i.val ∨ i.val < 30) → B4 i = B3 i := by
    intro i hi
    refine install_other sd B3 WD i (fun j hj => ?_)
    have h1 := congrArg Fin.val hj
    have h2 := sd_lt j
    have h3 : 30 ≤ (sd j).val := by simp only [sd]; split_ifs <;> omega
    omega
  have B4_36 : B4 36 = ZeroPadding.pad Rc (List.replicate (200*(K+1+1)) true) :=
    (install_slot sd sd_inj B3 WD ⟨5, by decide⟩).trans hD5
  have B4blank : ∀ i : Fin 57, 47 ≤ i.val → B4 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B4off i (Or.inl hi)).trans (B3blank i (by omega))
  have B4_0 : B4 0 = UnaryTemplate.tape q := (B4off 0 (Or.inr (by decide))).trans B3_0
  have B4_1 : B4 1 = ZeroPadding.pad Rc (List.replicate Ms true) := (B4off 1 (Or.inr (by decide))).trans B3_1
  -- e: tape (200(K+2))
  let oE : Fin 3 → List Bool := ![ZeroPadding.pad Rc (List.replicate (dv L q) true),
    ZeroPadding.pad Rc (UnaryTemplate.tape (dv L q + false.toNat)),
    ZeroPadding.pad Rc (List.replicate (dv L q+3) false)]
  have s5 := Dimension.dock0 (Uniform.stepT false (dv L q) Rc Rc Rc) se se_inj B4 (by
    intro j
    fin_cases j
    · exact B4_36
    · exact B4blank 47 (by decide)
    · exact B4blank 48 (by decide))
  let B5 := install se B4 oE
  have L5 := RowConst.long_install se se_inj B4 oE E Rc L4 (by
    intro j _
    fin_cases j <;> exact Uniform.long_pad Rc _)
  have B5off : ∀ i : Fin 57, i.val ≠ 36 → i.val ≠ 47 → i.val ≠ 48 → B5 i = B4 i := by
    intro i h1 h2 h3
    refine install_other se B4 oE i (fun k hk => ?_)
    have := congrArg Fin.val hk
    fin_cases k <;> simp [se] at this <;> omega
  have B5_47 : B5 47 = ZeroPadding.pad Rc (UnaryTemplate.tape (dv L q)) :=
    (install_slot se se_inj B4 oE 1).trans (by simp only [oE, Bool.toNat_false, Nat.add_zero]; rfl)
  have B5blank : ∀ i : Fin 57, 49 ≤ i.val → B5 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B5off i (by omega) (by omega) (by omega)).trans (B4blank i (by omega))
  have B5_0 : B5 0 = UnaryTemplate.tape q := (B5off 0 (by decide) (by decide) (by decide)).trans B4_0
  have B5_1 : B5 1 = ZeroPadding.pad Rc (List.replicate Ms true) :=
    (B5off 1 (by decide) (by decide) (by decide)).trans B4_1
  -- f: 1^q (output)
  let oF : Fin 3 → List Bool := ![ZeroPadding.pad 0 (UnaryTemplate.tape q),
    ZeroPadding.pad Rc (UWalkUnary.output false false q), ZeroPadding.pad Rc (List.replicate (q+2) false)]
  have s6 := Dimension.dock0 (RowConst.stepUW false false q 0 Rc Rc) sf sf_inj B5 (by
    intro j
    fin_cases j
    · exact B5_0.trans (ZeroPadding.pad_zero _).symm
    · exact B5blank 49 (by decide)
    · exact B5blank 50 (by decide))
  let B6 := install sf B5 oF
  have L6 := RowConst.long_install sf sf_inj B5 oF E Rc L5 (by
    intro j hj
    fin_cases j
    · exact absurd rfl hj
    all_goals exact Uniform.long_pad Rc _)
  have B6off : ∀ i : Fin 57, i.val ≠ 0 → i.val ≠ 49 → i.val ≠ 50 → B6 i = B5 i := by
    intro i h1 h2 h3
    refine install_other sf B5 oF i (fun k hk => ?_)
    have := congrArg Fin.val hk
    fin_cases k <;> simp [sf] at this <;> omega
  have B6_0 : B6 0 = UnaryTemplate.tape q :=
    (install_slot sf sf_inj B5 oF 0).trans (ZeroPadding.pad_zero _)
  have B6_49 : B6 49 = ZeroPadding.pad Rc (List.replicate q true) :=
    (install_slot sf sf_inj B5 oF 1).trans (by simp only [oF]; rw [RowConst.out_ff]; rfl)
  have B6blank : ∀ i : Fin 57, 51 ≤ i.val → B6 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B6off i (by omega) (by omega) (by omega)).trans (B5blank i (by omega))
  have B6_47 : B6 47 = ZeroPadding.pad Rc (UnaryTemplate.tape (dv L q)) :=
    (B6off 47 (by decide) (by decide) (by decide)).trans B5_47
  have B6_1 : B6 1 = ZeroPadding.pad Rc (List.replicate Ms true) :=
    (B6off 1 (by decide) (by decide) (by decide)).trans B5_1
  -- g: 1^(q/dv)
  have hdv : 0 < dv L q := by unfold dv; omega
  obtain ⟨WG, hGs, hG0, _, hG2, hGl⟩ := stepDiv q (dv L q) Rc hdv
  have s7 := Dimension.dock0 hGs sg sg_inj B6 (by
    intro j
    fin_cases j
    · exact B6_49
    · exact B6_47
    · exact B6blank 51 (by decide)
    · exact B6blank 52 (by decide))
  let B7 := install sg B6 WG
  have L7 := RowConst.long_install sg sg_inj B6 WG E Rc L6 (fun j _ => hGl j)
  have B7off : ∀ i : Fin 57, i.val ≠ 49 → i.val ≠ 47 → i.val ≠ 51 → i.val ≠ 52 → B7 i = B6 i := by
    intro i h1 h2 h3 h4
    refine install_other sg B6 WG i (fun k hk => ?_)
    have := congrArg Fin.val hk
    fin_cases k <;> simp [sg] at this <;> omega
  have B7_49 : B7 49 = ZeroPadding.pad Rc (List.replicate q true) := (install_slot sg sg_inj B6 WG 0).trans hG0
  have B7_51 : B7 51 = ZeroPadding.pad Rc (List.replicate (q / dv L q) true) :=
    (install_slot sg sg_inj B6 WG 2).trans hG2
  have B7blank : ∀ i : Fin 57, 53 ≤ i.val → B7 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B7off i (by omega) (by omega) (by omega) (by omega)).trans (B6blank i (by omega))
  have B7_0 : B7 0 = UnaryTemplate.tape q :=
    (B7off 0 (by decide) (by decide) (by decide) (by decide)).trans B6_0
  have B7_1 : B7 1 = ZeroPadding.pad Rc (List.replicate Ms true) :=
    (B7off 1 (by decide) (by decide) (by decide) (by decide)).trans B6_1
  -- h: tape Ms
  let oH : Fin 3 → List Bool := ![ZeroPadding.pad Rc (List.replicate Ms true),
    ZeroPadding.pad Rc (UnaryTemplate.tape (Ms + false.toNat)),
    ZeroPadding.pad Rc (List.replicate (Ms+3) false)]
  have s8 := Dimension.dock0 (Uniform.stepT false Ms Rc Rc Rc) sh sh_inj B7 (by
    intro j
    fin_cases j
    · exact B7_1
    · exact B7blank 53 (by decide)
    · exact B7blank 54 (by decide))
  let B8 := install sh B7 oH
  have L8 := RowConst.long_install sh sh_inj B7 oH E Rc L7 (by
    intro j _
    fin_cases j <;> exact Uniform.long_pad Rc _)
  have B8off : ∀ i : Fin 57, i.val ≠ 1 → i.val ≠ 53 → i.val ≠ 54 → B8 i = B7 i := by
    intro i h1 h2 h3
    refine install_other sh B7 oH i (fun k hk => ?_)
    have := congrArg Fin.val hk
    fin_cases k <;> simp [sh] at this <;> omega
  have B8_1 : B8 1 = ZeroPadding.pad Rc (List.replicate Ms true) := install_slot sh sh_inj B7 oH 0
  have B8_53 : B8 53 = ZeroPadding.pad Rc (UnaryTemplate.tape Ms) :=
    (install_slot sh sh_inj B7 oH 1).trans (by simp only [oH, Bool.toNat_false, Nat.add_zero]; rfl)
  have B8blank : ∀ i : Fin 57, 55 ≤ i.val → B8 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B8off i (by omega) (by omega) (by omega)).trans (B7blank i (by omega))
  have B8_51 : B8 51 = ZeroPadding.pad Rc (List.replicate (q / dv L q) true) :=
    (B8off 51 (by decide) (by decide) (by decide)).trans B7_51
  have B8_0 : B8 0 = UnaryTemplate.tape q := (B8off 0 (by decide) (by decide) (by decide)).trans B7_0
  have B8_49 : B8 49 = ZeroPadding.pad Rc (List.replicate q true) :=
    (B8off 49 (by decide) (by decide) (by decide)).trans B7_49
  -- i: the product
  let uD := q / dv L q
  let oI : Fin 4 → List Bool := ![ZeroPadding.pad Rc (List.replicate uD true),
    ZeroPadding.pad Rc (UnaryTemplate.tape Ms), ZeroPadding.pad Rc (List.replicate (uD*Ms) true),
    ZeroPadding.pad Rc (List.replicate (uD*(2*Ms+3)+2) false)]
  have s9 := Dimension.dock0 (stepProd uD Ms Rc) si si_inj B8 (by
    intro j
    fin_cases j
    · exact B8_51
    · exact B8_53
    · exact B8blank 55 (by decide)
    · exact B8blank 56 (by decide))
  let B9 := install si B8 oI
  have L9 := RowConst.long_install si si_inj B8 oI E Rc L8 (by
    intro j _
    fin_cases j <;> exact Uniform.long_pad Rc _)
  have B9off : ∀ i : Fin 57, i.val ≠ 51 → i.val ≠ 53 → i.val ≠ 55 → i.val ≠ 56 → B9 i = B8 i := by
    intro i h1 h2 h3 h4
    refine install_other si B8 oI i (fun k hk => ?_)
    have := congrArg Fin.val hk
    fin_cases k <;> simp [si] at this <;> omega
  refine ⟨B9, ((((((((s1.seq s2).seq s3).seq s4).seq s5).seq s6).seq s7).seq s8).seq s9), ?_, ?_, ?_, ?_, ?_⟩
  · exact (B9off 0 (by decide) (by decide) (by decide) (by decide)).trans B8_0
  · exact (B9off 1 (by decide) (by decide) (by decide) (by decide)).trans B8_1
  · exact (B9off 49 (by decide) (by decide) (by decide) (by decide)).trans B8_49
  · exact install_slot si si_inj B8 oI 2
  · intro i hi
    exact L9 i hi

end
end NearCubicWires.SourceConstruction.InitSlopes
end

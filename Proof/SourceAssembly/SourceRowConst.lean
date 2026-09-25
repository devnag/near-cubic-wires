import Proof.SourceAssembly.SourceRewindOnce

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open NearCubicWires.SupplierEstimator
namespace NearCubicWires.SourceConstruction.RowConst
noncomputable section

/-! ## 1. Padded stages -/

/-- `UWalkUnary`, padded per tape. -/
theorem stepUW (sen ext : Bool) (n c0 c1 c2 : ℕ) :
    Step (UWalkUnary.machine sen ext) (2*n+6) (fun _ => 0)
      ![ZeroPadding.pad c0 (UnaryTemplate.tape n), ZeroPadding.pad c1 [], ZeroPadding.pad c2 []]
      (fun _ => 0)
      ![ZeroPadding.pad c0 (UnaryTemplate.tape n), ZeroPadding.pad c1 (UWalkUnary.output sen ext n),
        ZeroPadding.pad c2 (List.replicate (n+2) false)] := by
  have h := (CloseoutFinalSelector.step_of_clock (UWalkUnary.ready sen ext (n+2) n)).pad ![c0, c1, c2]
  refine (h.congr_in rfl ?_).congr rfl ?_
  · funext i; fin_cases i <;> simp [UWalkUnary.input, RepairSource.CloseoutCapacity.Power.template_source]
  · funext i; fin_cases i <;> simp [UWalkUnary.result, RepairSource.CloseoutCapacity.Power.template_source]

theorem out_tf (n : ℕ) : UWalkUnary.output true false n = CompareMachine.word n := by
  simp [UWalkUnary.output, UWalkUnary.lead, CompareMachine.word]
theorem out_ff (n : ℕ) : UWalkUnary.output false false n = List.replicate n true := by
  simp [UWalkUnary.output, UWalkUnary.lead]
theorem out_ft (n : ℕ) : UWalkUnary.output false true n = List.replicate (n+1) true := by
  simp [UWalkUnary.output, UWalkUnary.lead]

/-- `SourceLiveCount.run`, padded by `Rc` everywhere. -/
theorem stepLC (q L Rc : ℕ) : ∃ W : Fin 27 → List Bool,
    Step (PCJ6e421fabe2aa4155_SourceLiveCount.machine L) (PCJ6e421fabe2aa4155_SourceLiveCount.budget q L)
      (fun _ => 0) (fun j => ZeroPadding.pad Rc (if j.val = 0 then CompareMachine.word q else []))
      (fun _ => 0) W ∧
    W 25 = ZeroPadding.pad Rc (UnaryTemplate.tape (normalizedLiveCount q L)) ∧
    (∀ j, Rc ≤ (W j).length) := by
  obtain ⟨W, h, h25⟩ := Dimension.stepB q L
  refine ⟨fun j => ZeroPadding.pad Rc (W j), h.pad (fun _ => Rc), ?_, ?_⟩
  · simp only [h25]
  · intro j; exact Uniform.long_pad Rc _

/-- `MatrixUnaryDifference`, padded `![0, Rc, Rc, Rc]`. -/
theorem stepCp (q K Rc : ℕ) (hK : K ≤ q) : ∃ W : Fin 4 → List Bool,
    Step MatrixUnaryDifference.resetMachine (2*q+8) (fun _ => 0)
      ![UnaryTemplate.tape q, ZeroPadding.pad Rc (UnaryTemplate.tape K), ZeroPadding.pad Rc [],
        ZeroPadding.pad Rc []] (fun _ => 0) W ∧
    W 0 = UnaryTemplate.tape q ∧ W 1 = ZeroPadding.pad Rc (UnaryTemplate.tape K) ∧
    W 2 = ZeroPadding.pad Rc (UnaryTemplate.tape (q-K)) ∧
    (∀ j, j ≠ 0 → Rc ≤ (W j).length) := by
  obtain ⟨W, h, h0, h1, h2⟩ := Dimension.stepC q K hK
  refine ⟨fun j => ZeroPadding.pad (![0, Rc, Rc, Rc] j) (W j), (h.pad ![0, Rc, Rc, Rc]).congr_in rfl ?_,
    ?_, ?_, ?_, ?_⟩
  · funext i; fin_cases i <;> simp
  · simp [h0]
  · simp [h1]
  · simp [h2]
  · intro j hj
    fin_cases j
    · exact absurd rfl hj
    all_goals exact Uniform.long_pad Rc _

/-- `PCPUnarySplit.split_run`, padded by `Rc`. -/
theorem stepSplit (n Rc : ℕ) : Step PCPUnarySplit.machine (2*n+4) (fun _ => 0)
    ![ZeroPadding.pad Rc (List.replicate n true), ZeroPadding.pad Rc [], ZeroPadding.pad Rc [],
      ZeroPadding.pad Rc []] (fun _ => 0)
    ![ZeroPadding.pad Rc (List.replicate n true), ZeroPadding.pad Rc (List.replicate ((n+1)/2) true),
      ZeroPadding.pad Rc (List.replicate (n/2) true), ZeroPadding.pad Rc (List.replicate (n+1) false)] := by
  have h := (CloseoutFinalSelector.step_of_clock (PCPUnarySplit.split_run n)).pad (fun _ => Rc)
  refine (h.congr_in rfl ?_).congr rfl ?_
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-- `copy_step`, padded by `Rc`. -/
theorem stepCopy (r Rc : ℕ) : Step ClockUnarySum.machine (2*r+6) (fun _ => 0)
    ![ZeroPadding.pad Rc (List.replicate r true), ZeroPadding.pad Rc [], ZeroPadding.pad Rc [],
      ZeroPadding.pad Rc []] (fun _ => 0)
    ![ZeroPadding.pad Rc (List.replicate r true), ZeroPadding.pad Rc [],
      ZeroPadding.pad Rc (List.replicate r true), ZeroPadding.pad Rc (List.replicate (r+2) false)] := by
  have h := (BlockPlatform.UnaryCalc.copy_step r).pad (fun _ => Rc)
  refine (h.congr_in rfl ?_).congr rfl ?_
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-- `poly_step 1 c`, padded by `Rc` everywhere (input included). -/
theorem stepPoly (c n Rc : ℕ) : ∃ W : Fin (BlockPlatform.UnaryCalc.tapes 1) → List Bool,
    Step (PCPSerializerCapacity.Power.machine 1 c) (PCPSerializerCapacity.Power.budget 1 c n)
      (fun _ => 0) (fun i => ZeroPadding.pad Rc (if i.val = 0 then List.replicate n true else []))
      (fun _ => 0) W ∧
    W ⟨0, by decide⟩ = ZeroPadding.pad Rc (List.replicate n true) ∧
    W ⟨5, by decide⟩ = ZeroPadding.pad Rc (List.replicate (c*(n+1)) true) ∧
    (∀ j, Rc ≤ (W j).length) := by
  obtain ⟨W, h, h0, h1⟩ := Dimension.stepG 1 c n
  refine ⟨fun j => ZeroPadding.pad Rc (W j), (h.pad (fun _ => Rc)).congr_in rfl ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [h0]
  · rw [show (⟨5, by decide⟩ : Fin (BlockPlatform.UnaryCalc.tapes 1)) = ⟨3+2*1, by decide⟩ from rfl]
    simp only [h1, pow_one]
  · intro j; exact Uniform.long_pad Rc _

/-! ## 2. Bookkeeping, generic in the universe -/

theorem long_install {t u : ℕ} (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (B : Fin u → List Bool) (loc : Fin t → List Bool) (E : Fin u → Prop) (Rc : ℕ)
    (hB : ∀ i, ¬ E i → Rc ≤ (B i).length) (hloc : ∀ j, ¬ E (slots j) → Rc ≤ (loc j).length) :
    ∀ i, ¬ E i → Rc ≤ (install slots B loc i).length := by
  intro i hEi
  by_cases h : ∃ j, slots j = i
  · obtain ⟨j, rfl⟩ := h
    rw [install_slot slots hi B loc j]
    exact hloc j hEi
  · rw [install_other slots B loc i (fun j hj => h ⟨j, hj⟩)]
    exact hB i hEi

/-! ## 3. The local layout (79 tapes) -/

def sA : Fin 3 → Fin 79 := ![0, 1, 2]
def sB : Fin 27 → Fin 79 := fun j => ⟨if j.val = 0 then 1 else 2 + j.val, by have := j.isLt; split_ifs <;> omega⟩
def sC : Fin 4 → Fin 79 := ![0, 27, 29, 30]
def sD : Fin 3 → Fin 79 := ![29, 31, 32]
def sE : Fin 4 → Fin 79 := ![31, 33, 34, 35]
def sF : Fin 4 → Fin 79 := ![33, 36, 37, 38]
def sG : Fin 4 → Fin 79 := ![33, 37, 39, 40]
def sH : Fin 3 → Fin 79 := ![27, 41, 42]
def sI : Fin (BlockPlatform.UnaryCalc.tapes 1) → Fin 79 := fun j => ⟨if j.val = 0 then 41 else 42 + j.val, by
  have := j.isLt
  simp only [BlockPlatform.UnaryCalc.tapes, RepairSource.ProjectionNormalization.DimensionPolynomial.tapes] at this
  split_ifs <;> omega⟩
def sJ : Fin 3 → Fin 79 := ![41, 58, 59]
def sK : Fin 3 → Fin 79 := ![58, 60, 61]
def sL : Fin (BlockPlatform.UnaryCalc.tapes 1) → Fin 79 := fun j => ⟨if j.val = 0 then 60 else 61 + j.val, by
  have := j.isLt
  simp only [BlockPlatform.UnaryCalc.tapes, RepairSource.ProjectionNormalization.DimensionPolynomial.tapes] at this
  split_ifs <;> omega⟩
def sM : Fin 4 → Fin 79 := ![66, 39, 77, 78]

theorem sA_inj : Function.Injective sA := by decide
theorem sB_inj : Function.Injective sB := by decide
theorem sC_inj : Function.Injective sC := by decide
theorem sD_inj : Function.Injective sD := by decide
theorem sE_inj : Function.Injective sE := by decide
theorem sF_inj : Function.Injective sF := by decide
theorem sG_inj : Function.Injective sG := by decide
theorem sH_inj : Function.Injective sH := by decide
theorem sI_inj : Function.Injective sI := by decide
theorem sJ_inj : Function.Injective sJ := by decide
theorem sK_inj : Function.Injective sK := by decide
theorem sL_inj : Function.Injective sL := by decide
theorem sM_inj : Function.Injective sM := by decide

def input (q Rc : ℕ) : Fin 79 → List Bool := fun i =>
  if i.val = 0 then UnaryTemplate.tape q else ZeroPadding.pad Rc []

def machine (L cM : ℕ) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine sA (UWalkUnary.machine true false))
    (RecoveryFocus.machine sB (PCJ6e421fabe2aa4155_SourceLiveCount.machine L)))
    (RecoveryFocus.machine sC MatrixUnaryDifference.resetMachine))
    (RecoveryFocus.machine sD (UWalkUnary.machine false false)))
    (RecoveryFocus.machine sE PCPUnarySplit.machine))
    (RecoveryFocus.machine sF ClockUnarySum.machine))
    (RecoveryFocus.machine sG ClockUnarySum.machine))
    (RecoveryFocus.machine sH (UWalkUnary.machine false false)))
    (RecoveryFocus.machine sI (PCPSerializerCapacity.Power.machine 1 cM)))
    (RecoveryFocus.machine sJ (DimensionTemplate.machine true)))
    (RecoveryFocus.machine sK (UWalkUnary.machine false true)))
    (RecoveryFocus.machine sL (PCPSerializerCapacity.Power.machine 1 3)))
    (RecoveryFocus.machine sM ClockUnarySum.machine)

def cost (L cM q : ℕ) : ℕ :=
  let K := normalizedLiveCount q L
  let s := q - K
  let c := (s+1)/2
  ((((((((((((2*q+6)+1+PCJ6e421fabe2aa4155_SourceLiveCount.budget q L)+1+(2*q+8))+1+(2*s+6))+1+
    (2*s+4))+1+(2*c+6))+1+(2*(c+c)+6))+1+(2*K+6))+1+PCPSerializerCapacity.Power.budget 1 cM K)+1+
    (2*K+8))+1+(2*(K+1)+6))+1+PCPSerializerCapacity.Power.budget 1 3 (K+2))+1+
    (2*(3*(K+2+1)+(c+c))+6)

/-! ## 4. The run -/

theorem const_run (L cM q Rc : ℕ) : ∃ W : Fin 79 → List Bool,
    Step (machine L cM) (cost L cM q) (fun _ => 0) (input q Rc) (fun _ => 0) W ∧
    W 47 = ZeroPadding.pad Rc (List.replicate (cM*(normalizedLiveCount q L+1)) true) ∧
    W 77 = ZeroPadding.pad Rc (List.replicate (3*(normalizedLiveCount q L+2+1) +
      ((q - normalizedLiveCount q L+1)/2 + (q - normalizedLiveCount q L+1)/2)) true) ∧
    W 0 = UnaryTemplate.tape q ∧
    (∀ i : Fin 79, i.val ≠ 0 → Rc ≤ (W i).length) := by
  have hK := normalizedLiveCount_le q L
  let E : Fin 79 → Prop := fun i => i.val = 0
  let B0 := input q Rc
  have L0 : ∀ i, ¬ E i → Rc ≤ (B0 i).length := by
    intro i hi
    simp only [E] at hi
    simp only [B0, input, if_neg hi]
    exact Uniform.long_pad Rc _
  have bl0 : ∀ i : Fin 79, i.val ≠ 0 → B0 i = ZeroPadding.pad Rc [] := by
    intro i hi
    simp only [B0, input, if_neg hi]
  -- A
  let oA : Fin 3 → List Bool := ![ZeroPadding.pad 0 (UnaryTemplate.tape q),
    ZeroPadding.pad Rc (UWalkUnary.output true false q), ZeroPadding.pad Rc (List.replicate (q+2) false)]
  have s1 := Dimension.dock0 (stepUW true false q 0 Rc Rc) sA sA_inj B0 (by
    intro j
    fin_cases j
    · exact (ZeroPadding.pad_zero _).symm
    · exact bl0 1 (by decide)
    · exact bl0 2 (by decide))
  let B1 := install sA B0 oA
  have L1 := long_install sA sA_inj B0 oA E Rc L0 (by
    intro j hj
    fin_cases j
    · exact absurd rfl hj
    all_goals exact Uniform.long_pad Rc _)
  -- B
  obtain ⟨WB, hBs, hB25, hBl⟩ := stepLC q L Rc
  have s2 := Dimension.dock0 hBs sB sB_inj B1 (by
    intro j
    by_cases hj : j.val = 0
    · have e : sB j = 1 := Fin.ext (by simp [sB, hj])
      rw [e, if_pos hj, ← out_tf]
      exact install_slot sA sA_inj B0 oA 1
    · have hj' := j.isLt
      have hv : (sB j).val = 2 + j.val := by simp [sB, hj]
      rw [if_neg hj]
      refine (install_other sA B0 oA _ ?_).trans (bl0 _ (by omega))
      intro k hk
      have := congrArg Fin.val hk
      fin_cases k <;> simp [sA] at this <;> omega)
  let B2 := install sB B1 WB
  have L2 := long_install sB sB_inj B1 WB E Rc L1 (fun j _ => hBl j)
  have sB_lt : ∀ j, (sB j).val < 29 := by
    intro j; have := j.isLt; simp only [sB]; split_ifs <;> omega
  have B2off : ∀ i : Fin 79, (29 ≤ i.val ∨ i.val = 0) → B2 i = B1 i := by
    intro i hi
    refine install_other sB B1 WB i (fun j hj => ?_)
    have h1 := congrArg Fin.val hj
    have h2 := sB_lt j
    have h3 : (sB j).val ≠ 0 := by simp only [sB]; split_ifs <;> omega
    omega
  have B1blank : ∀ i : Fin 79, 3 ≤ i.val → B1 i = ZeroPadding.pad Rc [] := by
    intro i hi
    refine (install_other sA B0 oA i (fun k hk => ?_)).trans (bl0 i (by omega))
    have := congrArg Fin.val hk
    fin_cases k <;> simp [sA] at this <;> omega
  have B2_0 : B2 0 = UnaryTemplate.tape q :=
    (B2off 0 (Or.inr rfl)).trans ((install_slot sA sA_inj B0 oA 0).trans (ZeroPadding.pad_zero _))
  have B2_27 : B2 27 = ZeroPadding.pad Rc (UnaryTemplate.tape (normalizedLiveCount q L)) :=
    (install_slot sB sB_inj B1 WB 25).trans hB25
  have B2blank : ∀ i : Fin 79, 29 ≤ i.val → B2 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B2off i (Or.inl hi)).trans (B1blank i (by omega))
  -- C
  obtain ⟨WC, hCs, hC0, hC1, hC2, hCl⟩ := stepCp q (normalizedLiveCount q L) Rc hK
  have s3 := Dimension.dock0 hCs sC sC_inj B2 (by
    intro j
    fin_cases j
    · exact B2_0
    · exact B2_27
    · exact B2blank 29 (by decide)
    · exact B2blank 30 (by decide))
  let B3 := install sC B2 WC
  have L3 := long_install sC sC_inj B2 WC E Rc L2 (by
    intro j hj
    by_cases h0 : j = 0
    · subst h0; exact absurd rfl hj
    · exact hCl j h0)
  have B3_0 : B3 0 = UnaryTemplate.tape q := (install_slot sC sC_inj B2 WC 0).trans hC0
  have B3_27 : B3 27 = ZeroPadding.pad Rc (UnaryTemplate.tape (normalizedLiveCount q L)) :=
    (install_slot sC sC_inj B2 WC 1).trans hC1
  have B3_29 : B3 29 = ZeroPadding.pad Rc (UnaryTemplate.tape (q - normalizedLiveCount q L)) :=
    (install_slot sC sC_inj B2 WC 2).trans hC2
  have B3blank : ∀ i : Fin 79, 31 ≤ i.val → B3 i = ZeroPadding.pad Rc [] := by
    intro i hi
    refine (install_other sC B2 WC i (fun k hk => ?_)).trans (B2blank i (by omega))
    have := congrArg Fin.val hk
    fin_cases k <;> simp [sC] at this <;> omega
  -- D
  let oD : Fin 3 → List Bool := ![ZeroPadding.pad Rc (UnaryTemplate.tape (q - normalizedLiveCount q L)),
    ZeroPadding.pad Rc (UWalkUnary.output false false (q - normalizedLiveCount q L)),
    ZeroPadding.pad Rc (List.replicate (q - normalizedLiveCount q L+2) false)]
  have s4 := Dimension.dock0 (stepUW false false (q - normalizedLiveCount q L) Rc Rc Rc) sD sD_inj B3 (by
    intro j
    fin_cases j
    · exact B3_29
    · exact B3blank 31 (by decide)
    · exact B3blank 32 (by decide))
  let B4 := install sD B3 oD
  have L4 := long_install sD sD_inj B3 oD E Rc L3 (by
    intro j _
    fin_cases j <;> exact Uniform.long_pad Rc _)
  have B4off : ∀ i : Fin 79, i.val ≠ 29 → i.val ≠ 31 → i.val ≠ 32 → B4 i = B3 i := by
    intro i h1 h2 h3
    refine install_other sD B3 oD i (fun k hk => ?_)
    have := congrArg Fin.val hk
    fin_cases k <;> simp [sD] at this <;> omega
  have B4_31 : B4 31 = ZeroPadding.pad Rc (List.replicate (q - normalizedLiveCount q L) true) :=
    (install_slot sD sD_inj B3 oD 1).trans (by simp only [oD]; rw [out_ff]; rfl)
  have B4blank : ∀ i : Fin 79, 33 ≤ i.val → B4 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B4off i (by omega) (by omega) (by omega)).trans (B3blank i (by omega))
  -- E: split
  let s := q - normalizedLiveCount q L
  let c := (s+1)/2
  let oE : Fin 4 → List Bool := ![ZeroPadding.pad Rc (List.replicate s true),
    ZeroPadding.pad Rc (List.replicate ((s+1)/2) true), ZeroPadding.pad Rc (List.replicate (s/2) true),
    ZeroPadding.pad Rc (List.replicate (s+1) false)]
  have s5 := Dimension.dock0 (stepSplit s Rc) sE sE_inj B4 (by
    intro j
    fin_cases j
    · exact B4_31
    · exact B4blank 33 (by decide)
    · exact B4blank 34 (by decide)
    · exact B4blank 35 (by decide))
  let B5 := install sE B4 oE
  have L5 := long_install sE sE_inj B4 oE E Rc L4 (by
    intro j _
    fin_cases j <;> exact Uniform.long_pad Rc _)
  have B5off : ∀ i : Fin 79, i.val ≠ 31 → i.val ≠ 33 → i.val ≠ 34 → i.val ≠ 35 → B5 i = B4 i := by
    intro i h1 h2 h3 h4
    refine install_other sE B4 oE i (fun k hk => ?_)
    have := congrArg Fin.val hk
    fin_cases k <;> simp [sE] at this <;> omega
  have B5_33 : B5 33 = ZeroPadding.pad Rc (List.replicate c true) := install_slot sE sE_inj B4 oE 1
  have B5blank : ∀ i : Fin 79, 36 ≤ i.val → B5 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B5off i (by omega) (by omega) (by omega) (by omega)).trans (B4blank i (by omega))
  -- F: copy c
  let oF : Fin 4 → List Bool := ![ZeroPadding.pad Rc (List.replicate c true), ZeroPadding.pad Rc [],
    ZeroPadding.pad Rc (List.replicate c true), ZeroPadding.pad Rc (List.replicate (c+2) false)]
  have s6 := Dimension.dock0 (stepCopy c Rc) sF sF_inj B5 (by
    intro j
    fin_cases j
    · exact B5_33
    · exact B5blank 36 (by decide)
    · exact B5blank 37 (by decide)
    · exact B5blank 38 (by decide))
  let B6 := install sF B5 oF
  have L6 := long_install sF sF_inj B5 oF E Rc L5 (by
    intro j _
    fin_cases j <;> exact Uniform.long_pad Rc _)
  have B6off : ∀ i : Fin 79, i.val ≠ 33 → i.val ≠ 36 → i.val ≠ 37 → i.val ≠ 38 → B6 i = B5 i := by
    intro i h1 h2 h3 h4
    refine install_other sF B5 oF i (fun k hk => ?_)
    have := congrArg Fin.val hk
    fin_cases k <;> simp [sF] at this <;> omega
  have B6blank : ∀ i : Fin 79, 39 ≤ i.val → B6 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B6off i (by omega) (by omega) (by omega) (by omega)).trans (B5blank i (by omega))
  -- G: c + c
  let oG : Fin 4 → List Bool := ![ZeroPadding.pad Rc (List.replicate c true),
    ZeroPadding.pad Rc (List.replicate c true), ZeroPadding.pad Rc (List.replicate (c+c) true),
    ZeroPadding.pad Rc (List.replicate (c+c+2) false)]
  have s7 := Dimension.dock0 (RowWidth.stepSp c c Rc) sG sG_inj B6 (by
    intro j
    fin_cases j
    · exact install_slot sF sF_inj B5 oF 0
    · exact install_slot sF sF_inj B5 oF 2
    · exact B6blank 39 (by decide)
    · exact B6blank 40 (by decide))
  let B7 := install sG B6 oG
  have L7 := long_install sG sG_inj B6 oG E Rc L6 (by
    intro j _
    fin_cases j <;> exact Uniform.long_pad Rc _)
  have B7off : ∀ i : Fin 79, i.val ≠ 33 → i.val ≠ 37 → i.val ≠ 39 → i.val ≠ 40 → B7 i = B6 i := by
    intro i h1 h2 h3 h4
    refine install_other sG B6 oG i (fun k hk => ?_)
    have := congrArg Fin.val hk
    fin_cases k <;> simp [sG] at this <;> omega
  have B7_39 : B7 39 = ZeroPadding.pad Rc (List.replicate (c+c) true) := install_slot sG sG_inj B6 oG 2
  have B7blank : ∀ i : Fin 79, 41 ≤ i.val → B7 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B7off i (by omega) (by omega) (by omega) (by omega)).trans (B6blank i (by omega))
  have B7_27 : B7 27 = ZeroPadding.pad Rc (UnaryTemplate.tape (normalizedLiveCount q L)) :=
    (B7off 27 (by decide) (by decide) (by decide) (by decide)).trans
      ((B6off 27 (by decide) (by decide) (by decide) (by decide)).trans
        ((B5off 27 (by decide) (by decide) (by decide) (by decide)).trans
          ((B4off 27 (by decide) (by decide) (by decide)).trans B3_27)))
  have B7_0 : B7 0 = UnaryTemplate.tape q :=
    (B7off 0 (by decide) (by decide) (by decide) (by decide)).trans
      ((B6off 0 (by decide) (by decide) (by decide) (by decide)).trans
        ((B5off 0 (by decide) (by decide) (by decide) (by decide)).trans
          ((B4off 0 (by decide) (by decide) (by decide)).trans B3_0)))
  -- H: 1^K
  let K := normalizedLiveCount q L
  let oH : Fin 3 → List Bool := ![ZeroPadding.pad Rc (UnaryTemplate.tape K),
    ZeroPadding.pad Rc (UWalkUnary.output false false K), ZeroPadding.pad Rc (List.replicate (K+2) false)]
  have s8 := Dimension.dock0 (stepUW false false K Rc Rc Rc) sH sH_inj B7 (by
    intro j
    fin_cases j
    · exact B7_27
    · exact B7blank 41 (by decide)
    · exact B7blank 42 (by decide))
  let B8 := install sH B7 oH
  have L8 := long_install sH sH_inj B7 oH E Rc L7 (by
    intro j _
    fin_cases j <;> exact Uniform.long_pad Rc _)
  have B8off : ∀ i : Fin 79, i.val ≠ 27 → i.val ≠ 41 → i.val ≠ 42 → B8 i = B7 i := by
    intro i h1 h2 h3
    refine install_other sH B7 oH i (fun k hk => ?_)
    have := congrArg Fin.val hk
    fin_cases k <;> simp [sH] at this <;> omega
  have B8_41 : B8 41 = ZeroPadding.pad Rc (List.replicate K true) :=
    (install_slot sH sH_inj B7 oH 1).trans (by simp only [oH]; rw [out_ff]; rfl)
  have B8blank : ∀ i : Fin 79, 43 ≤ i.val → B8 i = ZeroPadding.pad Rc [] :=
    fun i hi => (B8off i (by omega) (by omega) (by omega)).trans (B7blank i (by omega))
  
  obtain ⟨WI, hIs, hI0, hI5, hIl⟩ := stepPoly cM K Rc
  have s9 := Dimension.dock0 hIs sI sI_inj B8 (by
    intro j
    by_cases hj : j.val = 0
    · have e : sI j = 41 := Fin.ext (by simp [sI, hj])
      rw [e, if_pos hj]
      exact B8_41
    · have hj' := j.isLt
      simp only [RepairSource.ProjectionNormalization.DimensionPolynomial.tapes] at hj'
      rw [if_neg hj]
      exact B8blank _ (by simp [sI, hj]; omega))
  let B9 := install sI B8 WI
  have L9 := long_install sI sI_inj B8 WI E Rc L8 (fun j _ => hIl j)
  have sI_off : ∀ i : Fin 79, i.val ≠ 41 → (i.val < 43 ∨ 57 < i.val) → ∀ k, sI k ≠ i := by
    intro i h1 h2 k hk
    have hv := congrArg Fin.val hk
    have hk' := k.isLt
    simp only [sI, BlockPlatform.UnaryCalc.tapes,
      RepairSource.ProjectionNormalization.DimensionPolynomial.tapes] at hv hk'
    split_ifs at hv <;> omega
  have B9_47 : B9 47 = ZeroPadding.pad Rc (List.replicate (cM*(K+1)) true) :=
    (install_slot sI sI_inj B8 WI ⟨5, by decide⟩).trans hI5
  have B9_41 : B9 41 = ZeroPadding.pad Rc (List.replicate K true) :=
    (install_slot sI sI_inj B8 WI ⟨0, by decide⟩).trans hI0
  have B9blank : ∀ i : Fin 79, 58 ≤ i.val → B9 i = ZeroPadding.pad Rc [] :=
    fun i hi => (install_other sI B8 WI i (sI_off i (by omega) (by omega))).trans (B8blank i (by omega))
  -- J: tape (K+1)
  let oJ : Fin 3 → List Bool := ![ZeroPadding.pad Rc (List.replicate K true),
    ZeroPadding.pad Rc (UnaryTemplate.tape (K + true.toNat)), ZeroPadding.pad Rc (List.replicate (K+3) false)]
  have s10 := Dimension.dock0 (Uniform.stepT true K Rc Rc Rc) sJ sJ_inj B9 (by
    intro j
    fin_cases j
    · exact B9_41
    · exact B9blank 58 (by decide)
    · exact B9blank 59 (by decide))
  let B10 := install sJ B9 oJ
  have L10 := long_install sJ sJ_inj B9 oJ E Rc L9 (by
    intro j _
    fin_cases j <;> exact Uniform.long_pad Rc _)
  have B10_58 : B10 58 = ZeroPadding.pad Rc (UnaryTemplate.tape (K+1)) :=
    (install_slot sJ sJ_inj B9 oJ 1).trans (by simp [oJ])
  have B10off : ∀ i : Fin 79, i.val ≠ 41 → i.val ≠ 58 → i.val ≠ 59 → B10 i = B9 i := by
    intro i h1 h2 h3
    refine install_other sJ B9 oJ i (fun k hk => ?_)
    have := congrArg Fin.val hk
    fin_cases k <;> simp [sJ] at this <;> omega
  -- K: 1^(K+2)
  let oK : Fin 3 → List Bool := ![ZeroPadding.pad Rc (UnaryTemplate.tape (K+1)),
    ZeroPadding.pad Rc (UWalkUnary.output false true (K+1)), ZeroPadding.pad Rc (List.replicate (K+1+2) false)]
  have s11 := Dimension.dock0 (stepUW false true (K+1) Rc Rc Rc) sK sK_inj B10 (by
    intro j
    fin_cases j
    · exact B10_58
    · exact (B10off 60 (by decide) (by decide) (by decide)).trans (B9blank 60 (by decide))
    · exact (B10off 61 (by decide) (by decide) (by decide)).trans (B9blank 61 (by decide)))
  let B11 := install sK B10 oK
  have L11 := long_install sK sK_inj B10 oK E Rc L10 (by
    intro j _
    fin_cases j <;> exact Uniform.long_pad Rc _)
  have B11_60 : B11 60 = ZeroPadding.pad Rc (List.replicate (K+1+1) true) :=
    (install_slot sK sK_inj B10 oK 1).trans (by simp only [oK]; rw [out_ft]; rfl)
  have B11off : ∀ i : Fin 79, i.val ≠ 58 → i.val ≠ 60 → i.val ≠ 61 → B11 i = B10 i := by
    intro i h1 h2 h3
    refine install_other sK B10 oK i (fun k hk => ?_)
    have := congrArg Fin.val hk
    fin_cases k <;> simp [sK] at this <;> omega
  -- L: 1^(3(K+3))
  obtain ⟨WL, hLs, _, hL5, hLl⟩ := stepPoly 3 (K+1+1) Rc
  have s12 := Dimension.dock0 hLs sL sL_inj B11 (by
    intro j
    by_cases hj : j.val = 0
    · have e : sL j = 60 := Fin.ext (by simp [sL, hj])
      rw [e, if_pos hj]
      exact B11_60
    · have hj' := j.isLt
      simp only [RepairSource.ProjectionNormalization.DimensionPolynomial.tapes] at hj'
      rw [if_neg hj]
      have hv : (sL j).val = 61 + j.val := by simp [sL, hj]
      exact (B11off _ (by omega) (by omega) (by omega)).trans
        ((B10off _ (by omega) (by omega) (by omega)).trans (B9blank _ (by omega))))
  let B12 := install sL B11 WL
  have L12 := long_install sL sL_inj B11 WL E Rc L11 (fun j _ => hLl j)
  have sL_off : ∀ i : Fin 79, i.val ≠ 60 → (i.val < 62 ∨ 76 < i.val) → ∀ k, sL k ≠ i := by
    intro i h1 h2 k hk
    have hv := congrArg Fin.val hk
    have hk' := k.isLt
    simp only [sL, BlockPlatform.UnaryCalc.tapes,
      RepairSource.ProjectionNormalization.DimensionPolynomial.tapes] at hv hk'
    split_ifs at hv <;> omega
  have B12_66 : B12 66 = ZeroPadding.pad Rc (List.replicate (3*(K+1+1+1)) true) :=
    (install_slot sL sL_inj B11 WL ⟨5, by decide⟩).trans hL5
  have B12_39 : B12 39 = ZeroPadding.pad Rc (List.replicate (c+c) true) :=
    (install_other sL B11 WL _ (sL_off 39 (by decide) (by decide))).trans
      ((B11off 39 (by decide) (by decide) (by decide)).trans ((B10off 39 (by decide) (by decide) (by decide)).trans
        ((install_other sI B8 WI _ (sI_off 39 (by decide) (by decide))).trans
          ((B8off 39 (by decide) (by decide) (by decide)).trans B7_39))))
  have B12blank : ∀ i : Fin 79, 77 ≤ i.val → B12 i = ZeroPadding.pad Rc [] :=
    fun i hi => (install_other sL B11 WL i (sL_off i (by omega) (by omega))).trans
      ((B11off i (by omega) (by omega) (by omega)).trans ((B10off i (by omega) (by omega) (by omega)).trans
        (B9blank i (by omega))))
  -- M: U0
  let oM : Fin 4 → List Bool := ![ZeroPadding.pad Rc (List.replicate (3*(K+1+1+1)) true),
    ZeroPadding.pad Rc (List.replicate (c+c) true),
    ZeroPadding.pad Rc (List.replicate (3*(K+1+1+1)+(c+c)) true),
    ZeroPadding.pad Rc (List.replicate (3*(K+1+1+1)+(c+c)+2) false)]
  have s13 := Dimension.dock0 (RowWidth.stepSp (3*(K+1+1+1)) (c+c) Rc) sM sM_inj B12 (by
    intro j
    fin_cases j
    · exact B12_66
    · exact B12_39
    · exact B12blank 77 (by decide)
    · exact B12blank 78 (by decide))
  let B13 := install sM B12 oM
  have L13 := long_install sM sM_inj B12 oM E Rc L12 (by
    intro j _
    fin_cases j <;> exact Uniform.long_pad Rc _)
  refine ⟨B13, (((((((((((s1.seq s2).seq s3).seq s4).seq s5).seq s6).seq s7).seq s8).seq s9).seq s10).seq
    s11).seq s12).seq s13, ?_, ?_, ?_, ?_⟩
  · exact (install_other sM B12 oM _ (by decide)).trans ((install_other sL B11 WL _
      (sL_off 47 (by decide) (by decide))).trans ((B11off 47 (by decide) (by decide) (by decide)).trans
        ((B10off 47 (by decide) (by decide) (by decide)).trans B9_47)))
  · exact install_slot sM sM_inj B12 oM 2
  · exact (install_other sM B12 oM _ (by decide)).trans ((install_other sL B11 WL _
      (sL_off 0 (by decide) (by decide))).trans ((B11off 0 (by decide) (by decide) (by decide)).trans
        ((B10off 0 (by decide) (by decide) (by decide)).trans ((install_other sI B8 WI _
          (sI_off 0 (by decide) (by decide))).trans ((B8off 0 (by decide) (by decide) (by decide)).trans B7_0)))))
  · intro i hi
    exact L13 i hi

end
end NearCubicWires.SourceConstruction.RowConst
end

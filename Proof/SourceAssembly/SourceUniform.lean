import Proof.SourceAssembly.SourceOnce

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
namespace NearCubicWires.SourceConstruction.Uniform
noncomputable section

theorem pad_pad (a b : ℕ) (w : List Bool) :
    ZeroPadding.pad a (ZeroPadding.pad b w) = ZeroPadding.pad (max a b) w := by
  simp only [ZeroPadding.pad, List.length_append, List.length_replicate, List.append_assoc,
    List.replicate_append_replicate]
  congr 2
  omega

/-- The template is the padded word. -/
theorem tape_eq_pad (x : ℕ) : UnaryTemplate.tape x = ZeroPadding.pad (x+2) (CompareMachine.word x) := by
  simp [UnaryTemplate.tape, ZeroPadding.pad, CompareMachine.word]

/-! ## 1. The stages, padded -/

/-- `DimensionTemplate`, padded per tape. -/
theorem stepT (extra : Bool) (n c0 c1 c2 : ℕ) :
    Step (DimensionTemplate.machine extra) (2*n+8) (fun _ => 0)
      ![ZeroPadding.pad c0 (List.replicate n true), ZeroPadding.pad c1 [], ZeroPadding.pad c2 []]
      (fun _ => 0)
      ![ZeroPadding.pad c0 (List.replicate n true),
        ZeroPadding.pad c1 (UnaryTemplate.tape (n + extra.toNat)),
        ZeroPadding.pad c2 (List.replicate (n+3) false)] := by
  have h := (CloseoutFinalSelector.step_of_clock (DimensionTemplate.ready extra n)).pad ![c0, c1, c2]
  refine (h.congr_in rfl ?_).congr rfl ?_
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-- `poly_step 1 c`, padded by `Rc` on its workspace (input tape unpadded). -/
theorem stepP (c n Rc : ℕ) : ∃ W : Fin (BlockPlatform.UnaryCalc.tapes 1) → List Bool,
    Step (PCPSerializerCapacity.Power.machine 1 c) (PCPSerializerCapacity.Power.budget 1 c n)
      (fun _ => 0) (fun i => if i.val = 0 then List.replicate n true else List.replicate Rc false)
      (fun _ => 0) W ∧
    W ⟨0, by decide⟩ = List.replicate n true ∧
    W ⟨5, by decide⟩ = ZeroPadding.pad Rc (List.replicate (c*(n+1)) true) ∧
    (∀ i, i.val ≠ 0 → Rc ≤ (W i).length) := by
  obtain ⟨W, h, h0, h1⟩ := Dimension.stepG 1 c n
  refine ⟨fun i => ZeroPadding.pad (if i.val = 0 then 0 else Rc) (W i),
    (h.pad (fun i => if i.val = 0 then 0 else Rc)).congr_in rfl ?_, ?_, ?_, ?_⟩
  · funext i
    by_cases hi : i.val = 0
    · simp [hi]
    · simp [hi, ZeroPadding.pad]
  · simpa using h0
  · simp only [show (5 : ℕ) ≠ 0 by decide, if_false]
    rw [show (⟨5, by decide⟩ : Fin (BlockPlatform.UnaryCalc.tapes 1)) = ⟨3+2*1, by decide⟩ from rfl, h1]
    simp
  · intro i hi
    simp only [hi, if_false, ZeroPadding.pad_length]
    omega

/-! ## 2. The local layout -/

def psV (j : ℕ) : ℕ := if j = 0 then 0 else 10 + j
def prV (j : ℕ) : ℕ := if j = 0 then 0 else 25 + j
def psS : Fin (BlockPlatform.UnaryCalc.tapes 1) → Fin 43 := fun j => ⟨psV j.val, by
  have := j.isLt
  simp only [BlockPlatform.UnaryCalc.tapes, RepairSource.ProjectionNormalization.DimensionPolynomial.tapes] at this
  unfold psV; split_ifs <;> omega⟩
def psR : Fin (BlockPlatform.UnaryCalc.tapes 1) → Fin 43 := fun j => ⟨prV j.val, by
  have := j.isLt
  simp only [BlockPlatform.UnaryCalc.tapes, RepairSource.ProjectionNormalization.DimensionPolynomial.tapes] at this
  unfold prV; split_ifs <;> omega⟩

theorem psS_inj : Function.Injective psS := by
  intro a b h
  have hv := congrArg Fin.val h
  have ha := a.isLt; have hb := b.isLt
  simp only [psS, psV, BlockPlatform.UnaryCalc.tapes,
    RepairSource.ProjectionNormalization.DimensionPolynomial.tapes] at hv ha hb
  apply Fin.ext
  split_ifs at hv <;> omega

theorem psR_inj : Function.Injective psR := by
  intro a b h
  have hv := congrArg Fin.val h
  have ha := a.isLt; have hb := b.isLt
  simp only [psR, prV, BlockPlatform.UnaryCalc.tapes,
    RepairSource.ProjectionNormalization.DimensionPolynomial.tapes] at hv ha hb
  apply Fin.ext
  split_ifs at hv <;> omega

def t0 : Fin 3 → Fin 43 := ![15, 3, 7]
def t1 : Fin 3 → Fin 43 := ![30, 4, 8]
def t2 : Fin 3 → Fin 43 := ![0, 5, 9]
def t3 : Fin 3 → Fin 43 := ![2, 6, 10]

/-- The erase mask: `1^V` and its log. -/
def mask : Fin 43 → Bool := fun i => i.val = 0 || i.val = 1
/-- The head moves: the four drivers one cell right. -/
def dirs : Fin 43 → HeadMove := fun i => if 3 ≤ i.val ∧ i.val ≤ 6 then HeadMove.right else HeadMove.stay

def input (V VL b Rc : ℕ) : Fin 43 → List Bool := fun i =>
  if i.val = 0 then List.replicate V true
  else if i.val = 1 then List.replicate VL false
  else if i.val = 2 then List.replicate b true
  else if i.val = 41 then List.replicate Rc true
  else if i.val = 42 then List.replicate (Rc+2) false
  else List.replicate Rc false

def machine (cS cR : ℕ) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine psS (PCPSerializerCapacity.Power.machine 1 cS))
    (RecoveryFocus.machine t0 (DimensionTemplate.machine false)))
    (RecoveryFocus.machine psR (PCPSerializerCapacity.Power.machine 1 cR)))
    (RecoveryFocus.machine t1 (DimensionTemplate.machine false)))
    (RecoveryFocus.machine t2 (DimensionTemplate.machine true)))
    (RecoveryFocus.machine t3 (DimensionTemplate.machine false)))
    (CloseoutWitness.SelectedErase.machine mask (41 : Fin 43) (42 : Fin 43)))
    (DecompositionCountPosition.move dirs)

def cost (cS cR V b Rc : ℕ) : ℕ :=
  ((((((PCPSerializerCapacity.Power.budget 1 cS V+1+(2*(cS*(V+1))+8))+1+
    PCPSerializerCapacity.Power.budget 1 cR V)+1+(2*(cR*(V+1))+8))+1+(2*V+8))+1+(2*b+8))+1+
    (2*Rc+4))+1+1

/-- Final heads: the four drivers at `1`. -/
def outH : Fin 43 → ℕ := fun i => if 3 ≤ i.val ∧ i.val ≤ 6 then 1 else 0

/-! ## 3. The run -/

/-- Long tapes (`≥ Rc`) off an excluded set survive an install whose written tapes are long. -/
theorem long_install {t : ℕ} (slots : Fin t → Fin 43) (hi : Function.Injective slots)
    (B : Fin 43 → List Bool) (loc : Fin t → List Bool) (E : Fin 43 → Prop) (Rc : ℕ)
    (hB : ∀ i, ¬ E i → Rc ≤ (B i).length) (hloc : ∀ j, ¬ E (slots j) → Rc ≤ (loc j).length) :
    ∀ i, ¬ E i → Rc ≤ (install slots B loc i).length := by
  intro i hEi
  by_cases h : ∃ j, slots j = i
  · obtain ⟨j, rfl⟩ := h
    rw [install_slot slots hi B loc j]
    exact hloc j hEi
  · rw [install_other slots B loc i (fun j hj => h ⟨j, hj⟩)]
    exact hB i hEi

theorem t_inj0 : Function.Injective t0 := by decide
theorem t_inj1 : Function.Injective t1 := by decide
theorem t_inj2 : Function.Injective t2 := by decide
theorem t_inj3 : Function.Injective t3 := by decide

theorem pad_blank (Rc : ℕ) : List.replicate Rc false = ZeroPadding.pad Rc [] := by
  simp [ZeroPadding.pad]

theorem off {t : ℕ} (slots : Fin t → Fin 43) (B : Fin 43 → List Bool) (loc : Fin t → List Bool)
    (i : Fin 43) (h : ∀ j, slots j ≠ i) : install slots B loc i = B i :=
  install_other slots B loc i h

theorem long_pad (Rc : ℕ) (w : List Bool) : Rc ≤ (ZeroPadding.pad Rc w).length := by
  rw [ZeroPadding.pad_length]; omega

/-- **The uniform drivers, once.** From `once_run`'s leftovers on the 43 local tapes, all heads `0`,
the run reaches:
- `S`, `R`, `B = V+1` and `b` as padded templates on tapes `3..6`, heads `1`;
- `1^V` and its log erased to `replicate Rc false`;
- the width driver unchanged, and the clear's driver and log unchanged;
- every tape but the read-only width driver of length `≥ Rc` (the first-call reserve). -/
theorem uniform_run (cS cR V VL b Rc : ℕ) (hV : V ≤ Rc) (hVL : VL ≤ Rc) :
    ∃ W : Fin 43 → List Bool,
      Step (machine cS cR) (cost cS cR V b Rc) (fun _ => 0) (input V VL b Rc) outH W ∧
      W 3 = ZeroPadding.pad Rc (UnaryTemplate.tape (cS*(V+1))) ∧
      W 4 = ZeroPadding.pad Rc (UnaryTemplate.tape (cR*(V+1))) ∧
      W 5 = ZeroPadding.pad Rc (UnaryTemplate.tape (V+1)) ∧
      W 6 = ZeroPadding.pad Rc (UnaryTemplate.tape b) ∧
      W 0 = List.replicate Rc false ∧ W 1 = List.replicate Rc false ∧
      W 2 = List.replicate b true ∧
      W 41 = List.replicate Rc true ∧ W 42 = List.replicate (Rc+2) false ∧
      (∀ i : Fin 43, i.val ≠ 2 → Rc ≤ (W i).length) := by
  let E : Fin 43 → Prop := fun i => i.val = 0 ∨ i.val = 1 ∨ i.val = 2
  let B0 := input V VL b Rc
  have L0 : ∀ i, ¬ E i → Rc ≤ (B0 i).length := by
    intro i hi
    simp only [E, not_or] at hi
    simp only [B0, input, if_neg hi.1, if_neg hi.2.1, if_neg hi.2.2]
    split_ifs <;> simp
  -- U1: S-poly
  obtain ⟨W1, h1, h10, h15, hl1⟩ := stepP cS V Rc
  have s1 := Dimension.dock0 h1 psS psS_inj B0 (by
    intro j
    by_cases hj : j.val = 0
    · simp [B0, input, psS, psV, hj]
    · have hj' := j.isLt
      simp only [RepairSource.ProjectionNormalization.DimensionPolynomial.tapes] at hj'
      simp only [B0, input, psS, psV, hj, if_false]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)])
  let B1 := install psS B0 W1
  have B1_0 : B1 0 = List.replicate V true := (install_slot psS psS_inj B0 W1 ⟨0, by decide⟩).trans h10
  have B1_15 : B1 15 = ZeroPadding.pad Rc (List.replicate (cS*(V+1)) true) :=
    (install_slot psS psS_inj B0 W1 ⟨5, by decide⟩).trans h15
  have B1off : ∀ i : Fin 43, (i.val < 11 ∨ 25 < i.val) → i.val ≠ 0 → B1 i = B0 i := by
    intro i hi h0
    refine install_other psS B0 W1 i (fun j hj => ?_)
    have hv := congrArg Fin.val hj
    have hj' := j.isLt
    simp only [psS, psV, BlockPlatform.UnaryCalc.tapes,
      RepairSource.ProjectionNormalization.DimensionPolynomial.tapes] at hv hj'
    split_ifs at hv <;> omega
  have L1 := long_install psS psS_inj B0 W1 E Rc L0 (by
    intro j hj
    by_cases h0 : j.val = 0
    · exact absurd (Or.inl (by simp [psS, psV, h0])) hj
    · exact hl1 j h0)
  have B0blank : ∀ i : Fin 43, i.val ≠ 0 → i.val ≠ 1 → i.val ≠ 2 → i.val ≠ 41 → i.val ≠ 42 →
      B0 i = ZeroPadding.pad Rc [] := by
    intro i h0 h1 h2 h41 h42
    simp only [B0, input, if_neg h0, if_neg h1, if_neg h2, if_neg h41, if_neg h42]
    exact pad_blank Rc
  -- U2: template S
  let oT0 : Fin 3 → List Bool := ![ZeroPadding.pad Rc (List.replicate (cS*(V+1)) true),
    ZeroPadding.pad Rc (UnaryTemplate.tape (cS*(V+1) + false.toNat)),
    ZeroPadding.pad Rc (List.replicate (cS*(V+1)+3) false)]
  have s2 := Dimension.dock0 (stepT false (cS*(V+1)) Rc Rc Rc) t0 t_inj0 B1 (by
    intro j
    fin_cases j
    · exact B1_15
    · exact (B1off 3 (by decide) (by decide)).trans (B0blank 3 (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact (B1off 7 (by decide) (by decide)).trans (B0blank 7 (by decide) (by decide) (by decide) (by decide) (by decide)))
  let B2 := install t0 B1 oT0
  have L2 := long_install t0 t_inj0 B1 oT0 E Rc L1 (by
    intro j _
    fin_cases j <;> exact long_pad _ _)
  -- U3: R-poly
  obtain ⟨W3, h3, h30, h35, hl3⟩ := stepP cR V Rc
  have ht0 : ∀ k, (t0 k).val < 16 := by decide
  have s3 := Dimension.dock0 h3 psR psR_inj B2 (by
    intro j
    by_cases hj : j.val = 0
    · have e : psR j = 0 := Fin.ext (by simp [psR, prV, hj])
      rw [e]
      refine ((off t0 B1 oT0 0 (by decide)).trans B1_0).trans ?_
      simp [hj]
    · have hj' := j.isLt
      simp only [RepairSource.ProjectionNormalization.DimensionPolynomial.tapes] at hj'
      have hv : (psR j).val = 25 + j.val := by simp [psR, prV, hj]
      have hne : ∀ k, t0 k ≠ psR j := by
        intro k hk
        have h1 := congrArg Fin.val hk
        have h2 := ht0 k
        omega
      refine (off t0 B1 oT0 _ hne).trans ((B1off _ (by omega) (by omega)).trans
        ((B0blank _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans ?_))
      simp [hj, ZeroPadding.pad])
  let B3 := install psR B2 W3
  have L3 := long_install psR psR_inj B2 W3 E Rc L2 (by
    intro j hj
    by_cases h0 : j.val = 0
    · exact absurd (Or.inl (by simp [psR, prV, h0])) hj
    · exact hl3 j h0)
  -- U4: template R
  let oT1 : Fin 3 → List Bool := ![ZeroPadding.pad Rc (List.replicate (cR*(V+1)) true),
    ZeroPadding.pad Rc (UnaryTemplate.tape (cR*(V+1) + false.toNat)),
    ZeroPadding.pad Rc (List.replicate (cR*(V+1)+3) false)]
  have psR_off : ∀ i : Fin 43, i.val ≠ 0 → (i.val < 26 ∨ 40 < i.val) → ∀ j, psR j ≠ i := by
    intro i h0 hi j hj
    have hv := congrArg Fin.val hj
    have hj' := j.isLt
    simp only [psR, prV, RepairSource.ProjectionNormalization.DimensionPolynomial.tapes] at hv hj'
    split_ifs at hv <;> omega
  have s4 := Dimension.dock0 (stepT false (cR*(V+1)) Rc Rc Rc) t1 t_inj1 B3 (by
    intro j
    fin_cases j
    · exact (install_slot psR psR_inj B2 W3 ⟨5, by decide⟩).trans h35
    · exact (off psR B2 W3 4 (psR_off 4 (by decide) (by decide))).trans
        ((off t0 B1 oT0 4 (by decide)).trans ((B1off 4 (by decide) (by decide)).trans
          (B0blank 4 (by decide) (by decide) (by decide) (by decide) (by decide))))
    · exact (off psR B2 W3 8 (psR_off 8 (by decide) (by decide))).trans
        ((off t0 B1 oT0 8 (by decide)).trans ((B1off 8 (by decide) (by decide)).trans
          (B0blank 8 (by decide) (by decide) (by decide) (by decide) (by decide)))))
  let B4 := install t1 B3 oT1
  have L4 := long_install t1 t_inj1 B3 oT1 E Rc L3 (by
    intro j _
    fin_cases j <;> exact long_pad _ _)
  -- U5: template V+1 (B)
  have B4_0 : B4 0 = List.replicate V true :=
    (off t1 B3 oT1 0 (by decide)).trans ((install_slot psR psR_inj B2 W3 ⟨0, by decide⟩).trans h30)
  let oT2 : Fin 3 → List Bool := ![ZeroPadding.pad 0 (List.replicate V true),
    ZeroPadding.pad Rc (UnaryTemplate.tape (V + true.toNat)),
    ZeroPadding.pad Rc (List.replicate (V+3) false)]
  have blankChain : ∀ i : Fin 43, i.val ≠ 0 → i.val ≠ 1 → i.val ≠ 2 → i.val ≠ 41 → i.val ≠ 42 →
      (∀ j, t1 j ≠ i) → (i.val < 26 ∨ 40 < i.val) → (∀ j, t0 j ≠ i) → (i.val < 11 ∨ 25 < i.val) →
      B4 i = ZeroPadding.pad Rc [] := by
    intro i h0 h1 h2 h41 h42 ht1 hR ht0 hS
    exact (off t1 B3 oT1 i ht1).trans ((off psR B2 W3 i (psR_off i h0 hR)).trans
      ((off t0 B1 oT0 i ht0).trans ((B1off i hS h0).trans (B0blank i h0 h1 h2 h41 h42))))
  have s5 := Dimension.dock0 (stepT true V 0 Rc Rc) t2 t_inj2 B4 (by
    intro j
    fin_cases j
    · exact B4_0.trans (ZeroPadding.pad_zero _).symm
    · exact blankChain 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    · exact blankChain 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide))
  let B5 := install t2 B4 oT2
  have L5 := long_install t2 t_inj2 B4 oT2 E Rc L4 (by
    intro j hj
    fin_cases j
    · exact absurd (Or.inl rfl) hj
    · exact long_pad _ _
    · exact long_pad _ _)
  -- U6: template b (v)
  let oT3 : Fin 3 → List Bool := ![ZeroPadding.pad 0 (List.replicate b true),
    ZeroPadding.pad Rc (UnaryTemplate.tape (b + false.toNat)),
    ZeroPadding.pad Rc (List.replicate (b+3) false)]
  have B4_2 : B4 2 = List.replicate b true :=
    (off t1 B3 oT1 2 (by decide)).trans ((off psR B2 W3 2 (psR_off 2 (by decide) (by decide))).trans
      ((off t0 B1 oT0 2 (by decide)).trans ((B1off 2 (by decide) (by decide)).trans
        (by simp [B0, input]))))
  have s6 := Dimension.dock0 (stepT false b 0 Rc Rc) t3 t_inj3 B5 (by
    intro j
    fin_cases j
    · exact (off t2 B4 oT2 2 (by decide)).trans (B4_2.trans (ZeroPadding.pad_zero _).symm)
    · exact (off t2 B4 oT2 6 (by decide)).trans (blankChain 6 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact (off t2 B4 oT2 10 (by decide)).trans (blankChain 10 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
  let B6 := install t3 B5 oT3
  have L6 := long_install t3 t_inj3 B5 oT3 E Rc L5 (by
    intro j hj
    fin_cases j
    · exact absurd (Or.inr (Or.inr rfl)) hj
    · exact long_pad _ _
    · exact long_pad _ _)
  -- the values that survive to the end
  have B6_0 : B6 0 = List.replicate V true :=
    (off t3 B5 oT3 0 (by decide)).trans ((install_slot t2 t_inj2 B4 oT2 0).trans (ZeroPadding.pad_zero _))
  have B6_1 : B6 1 = List.replicate VL false :=
    (off t3 B5 oT3 1 (by decide)).trans ((off t2 B4 oT2 1 (by decide)).trans
      ((off t1 B3 oT1 1 (by decide)).trans ((off psR B2 W3 1 (psR_off 1 (by decide) (by decide))).trans
        ((off t0 B1 oT0 1 (by decide)).trans ((B1off 1 (by decide) (by decide)).trans
          (by simp [B0, input]))))))
  have B6_2 : B6 2 = List.replicate b true :=
    (install_slot t3 t_inj3 B5 oT3 0).trans (ZeroPadding.pad_zero _)
  have B6_41 : B6 41 = List.replicate Rc true :=
    (off t3 B5 oT3 41 (by decide)).trans ((off t2 B4 oT2 41 (by decide)).trans
      ((off t1 B3 oT1 41 (by decide)).trans ((off psR B2 W3 41 (psR_off 41 (by decide) (by decide))).trans
        ((off t0 B1 oT0 41 (by decide)).trans ((B1off 41 (by decide) (by decide)).trans
          (by simp [B0, input]))))))
  have B6_42 : B6 42 = List.replicate (Rc+2) false :=
    (off t3 B5 oT3 42 (by decide)).trans ((off t2 B4 oT2 42 (by decide)).trans
      ((off t1 B3 oT1 42 (by decide)).trans ((off psR B2 W3 42 (psR_off 42 (by decide) (by decide))).trans
        ((off t0 B1 oT0 42 (by decide)).trans ((B1off 42 (by decide) (by decide)).trans
          (by simp [B0, input]))))))
  have B6_3 : B6 3 = ZeroPadding.pad Rc (UnaryTemplate.tape (cS*(V+1))) := by
    refine (off t3 B5 oT3 3 (by decide)).trans ((off t2 B4 oT2 3 (by decide)).trans
      ((off t1 B3 oT1 3 (by decide)).trans ((off psR B2 W3 3 (psR_off 3 (by decide) (by decide))).trans
        ((install_slot t0 t_inj0 B1 oT0 1).trans ?_))))
    simp [oT0]
  have B6_4 : B6 4 = ZeroPadding.pad Rc (UnaryTemplate.tape (cR*(V+1))) := by
    refine (off t3 B5 oT3 4 (by decide)).trans ((off t2 B4 oT2 4 (by decide)).trans
      ((install_slot t1 t_inj1 B3 oT1 1).trans ?_))
    simp [oT1]
  have B6_5 : B6 5 = ZeroPadding.pad Rc (UnaryTemplate.tape (V+1)) := by
    refine (off t3 B5 oT3 5 (by decide)).trans ((install_slot t2 t_inj2 B4 oT2 1).trans ?_)
    simp [oT2]
  have B6_6 : B6 6 = ZeroPadding.pad Rc (UnaryTemplate.tape b) := by
    refine (install_slot t3 t_inj3 B5 oT3 1).trans ?_
    simp [oT3]
  -- U7: erase `1^V` and its log
  have s7 := BlockPlatform.Scrub.erase_step mask (41 : Fin 43) (42 : Fin 43) (by decide) (by decide)
    (by decide) Rc (Rc+2) (by omega) (fun _ => 0) B6 (fun _ _ => rfl) (by
      intro i hi
      simp only [mask, Bool.or_eq_true, decide_eq_true_eq] at hi
      rcases hi with hi | hi
      · rw [show i = 0 from Fin.ext hi, B6_0]; simp [hV]
      · rw [show i = 1 from Fin.ext hi, B6_1]; simp [hVL]) B6_41 B6_42
  let B7 := BlockPlatform.Scrub.blank mask B6 Rc
  -- U8: drivers' heads to 1
  obtain ⟨r, hr, hf, hs⟩ := DecompositionCountPosition.move_run dirs (fun _ => 0) B7
  have s8 : Step (DecompositionCountPosition.move dirs) 1 (fun _ => 0) B7 outH B7 := by
    refine ⟨r, hr, ?_, ?_, le_of_eq hs⟩
    · rw [hf]
      funext i
      simp only [dirs, outH]
      split_ifs <;> rfl
    · rw [hf]
  have hm : ∀ i : Fin 43, i.val ≠ 0 → i.val ≠ 1 → mask i = false := by
    intro i h0 h1
    simp [mask, h0, h1]
  refine ⟨B7, ((((((((s1.seq s2).seq s3).seq s4).seq s5).seq s6).seq s7).seq s8)), ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [B7, BlockPlatform.Scrub.blank, hm 3 (by decide) (by decide), Bool.false_eq_true, if_false]
    exact B6_3
  · simp only [B7, BlockPlatform.Scrub.blank, hm 4 (by decide) (by decide), Bool.false_eq_true, if_false]
    exact B6_4
  · simp only [B7, BlockPlatform.Scrub.blank, hm 5 (by decide) (by decide), Bool.false_eq_true, if_false]
    exact B6_5
  · simp only [B7, BlockPlatform.Scrub.blank, hm 6 (by decide) (by decide), Bool.false_eq_true, if_false]
    exact B6_6
  · simp [B7, BlockPlatform.Scrub.blank, mask]
  · simp [B7, BlockPlatform.Scrub.blank, mask]
  · simp only [B7, BlockPlatform.Scrub.blank, hm 2 (by decide) (by decide), Bool.false_eq_true, if_false]
    exact B6_2
  · simp only [B7, BlockPlatform.Scrub.blank, hm 41 (by decide) (by decide), Bool.false_eq_true, if_false]
    exact B6_41
  · simp only [B7, BlockPlatform.Scrub.blank, hm 42 (by decide) (by decide), Bool.false_eq_true, if_false]
    exact B6_42
  · intro i h2
    simp only [B7, BlockPlatform.Scrub.blank]
    split_ifs with hmi
    · simp
    · have h0 : i.val ≠ 0 := fun h => hmi (by simp [mask, h])
      have h1 : i.val ≠ 1 := fun h => hmi (by simp [mask, h])
      exact L6 i (by simp only [E]; omega)

end
end NearCubicWires.SourceConstruction.Uniform
end

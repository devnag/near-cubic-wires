import Proof.SourceAssembly.SourceUniform

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open NearCubicWires.SupplierEstimator PCJ9eff70d512234a4c_Fixed
namespace NearCubicWires.SourceConstruction.RowWidth
noncomputable section

/-! ## 1. The value `rowWidth` is forced to -/

/-- The calculator's value. -/
def rw (M2 U0 L : ℕ) : ℕ := M2 * (L+1) + U0

/-! ## 2. Padded stages -/

theorem pad_word_template (e Rc : ℕ) (he : e + 2 ≤ Rc) :
    ZeroPadding.pad Rc (UnaryTemplate.tape e) = ZeroPadding.pad Rc (false :: List.replicate e true) := by
  rw [show UnaryTemplate.tape e = ZeroPadding.pad (e+2) (false :: List.replicate e true) by
    simp [UnaryTemplate.tape, ZeroPadding.pad], Uniform.pad_pad, max_eq_left he]

/-- `product_step`, padded by `Rc` on all four tapes. -/
theorem stepHp (d e Rc : ℕ) : Step ClockUnaryProduct.machine (2*(d*(2*e+3)+2)+2) (fun _ => 0)
    ![ZeroPadding.pad Rc (List.replicate d true), ZeroPadding.pad Rc (false :: List.replicate e true),
      ZeroPadding.pad Rc [], ZeroPadding.pad Rc []] (fun _ => 0)
    ![ZeroPadding.pad Rc (List.replicate d true), ZeroPadding.pad Rc (false :: List.replicate e true),
      ZeroPadding.pad Rc (List.replicate (d*e) true),
      ZeroPadding.pad Rc (List.replicate (d*(2*e+3)+2) false)] := by
  have h := (BlockPlatform.UnaryCalc.product_step d e).pad (fun _ => Rc)
  refine (h.congr_in rfl ?_).congr rfl ?_
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-- `sum_step`, padded by `Rc` on all four tapes. -/
theorem stepSp (x y Rc : ℕ) : Step ClockUnarySum.machine (2*(x+y)+6) (fun _ => 0)
    ![ZeroPadding.pad Rc (List.replicate x true), ZeroPadding.pad Rc (List.replicate y true),
      ZeroPadding.pad Rc [], ZeroPadding.pad Rc []] (fun _ => 0)
    ![ZeroPadding.pad Rc (List.replicate x true), ZeroPadding.pad Rc (List.replicate y true),
      ZeroPadding.pad Rc (List.replicate (x+y) true), ZeroPadding.pad Rc (List.replicate (x+y+2) false)] := by
  have h := (BlockPlatform.UnaryCalc.sum_step x y).pad (fun _ => Rc)
  refine (h.congr_in rfl ?_).congr rfl ?_
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-! ## 3. The calculator -/

def sa : Fin 3 → Fin 16 := ![0, 6, 7]
def sb : Fin 4 → Fin 16 := ![1, 6, 8, 9]
def sc : Fin 4 → Fin 16 := ![8, 2, 10, 11]
def sd : Fin 3 → Fin 16 := ![10, 4, 12]
def sf : Fin 4 → Fin 16 := ![10, 3, 13, 14]
def sg : Fin 3 → Fin 16 := ![13, 5, 15]
def dirIn : Fin 16 → HeadMove := fun i => if i.val = 3 then HeadMove.left else HeadMove.stay
def dirOut : Fin 16 → HeadMove := fun i => if 3 ≤ i.val ∧ i.val ≤ 5 then HeadMove.right else HeadMove.stay

def inH : Fin 16 → ℕ := fun i => if i.val = 3 then 1 else 0
def outH : Fin 16 → ℕ := fun i => if 3 ≤ i.val ∧ i.val ≤ 5 then 1 else 0

/-- The input: `1^L`, the two uniform values and the counter, all padded; the rest blank
(`replicate Rc false`, the clear's exit). -/
def input (L M2 U0 N Rc : ℕ) : Fin 16 → List Bool := fun i =>
  if i.val = 0 then List.replicate L true
  else if i.val = 1 then ZeroPadding.pad Rc (List.replicate M2 true)
  else if i.val = 2 then ZeroPadding.pad Rc (List.replicate U0 true)
  else if i.val = 3 then ZeroPadding.pad Rc (CompareMachine.word N)
  else ZeroPadding.pad Rc []

def machine :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine sa (DimensionTemplate.machine true))
    (RecoveryFocus.machine sb ClockUnaryProduct.machine))
    (RecoveryFocus.machine sc ClockUnarySum.machine))
    (RecoveryFocus.machine sd (DimensionTemplate.machine false)))
    (DecompositionCountPosition.move dirIn))
    (RecoveryFocus.machine sf ClockUnaryProduct.machine))
    (RecoveryFocus.machine sg (DimensionTemplate.machine false)))
    (DecompositionCountPosition.move dirOut)

def cost (L M2 U0 N : ℕ) : ℕ :=
  let ca := 2*L+8
  let cb := 2*(M2*(2*(L+1)+3)+2)+2
  let cc := 2*(M2*(L+1)+U0)+6
  let cd := 2*rw M2 U0 L+8
  let cf := 2*(rw M2 U0 L*(2*N+3)+2)+2
  let cg := 2*(rw M2 U0 L*N)+8
  ((((((ca+1+cb)+1+cc)+1+cd)+1+1)+1+cf)+1+cg)+1+1

theorem moveStep {t : ℕ} (dirs : Fin t → HeadMove) (H : Fin t → ℕ) (A : Fin t → List Bool) :
    Step (DecompositionCountPosition.move dirs) 1 H A (fun i => (dirs i).apply (H i)) A := by
  obtain ⟨r, hr, hf, hs⟩ := DecompositionCountPosition.move_run dirs H A
  exact ⟨r, hr, by rw [hf], by rw [hf], le_of_eq hs⟩

theorem sa_inj : Function.Injective sa := by decide
theorem sb_inj : Function.Injective sb := by decide
theorem sc_inj : Function.Injective sc := by decide
theorem sd_inj : Function.Injective sd := by decide
theorem sf_inj : Function.Injective sf := by decide
theorem sg_inj : Function.Injective sg := by decide

theorem dock_inH {t s n : ℕ} {p : Machine t s} {tin tout : Fin t → List Bool}
    (h : Step p n (fun _ => 0) tin (fun _ => 0) tout) (slots : Fin t → Fin 16)
    (hi : Function.Injective slots) (h3 : ∀ j, (slots j).val ≠ 3) (A : Fin 16 → List Bool)
    (hA : ∀ j, A (slots j) = tin j) :
    Step (RecoveryFocus.machine slots p) n inH A inH (install slots A tout) := by
  have hz : ∀ j, inH (slots j) = 0 := fun j => by simp [inH, h3 j]
  have hs := h.dock slots hi inH A hz hA
  rwa [BlockPlatform.dockH_existing slots inH (fun _ => 0) hz] at hs

theorem calc_run (L M2 U0 N Rc : ℕ) (hL : L + 3 ≤ Rc) :
    ∃ W : Fin 16 → List Bool,
      Step machine (cost L M2 U0 N) inH (input L M2 U0 N Rc) outH W ∧
      W 4 = ZeroPadding.pad Rc (UnaryTemplate.tape (rw M2 U0 L)) ∧
      W 5 = ZeroPadding.pad Rc (UnaryTemplate.tape (rw M2 U0 L * N)) ∧
      W 3 = ZeroPadding.pad Rc (CompareMachine.word N) := by
  let B0 := input L M2 U0 N Rc
  -- a: tape (L+1)
  let oa : Fin 3 → List Bool := ![ZeroPadding.pad 0 (List.replicate L true),
    ZeroPadding.pad Rc (UnaryTemplate.tape (L + true.toNat)), ZeroPadding.pad Rc (List.replicate (L+3) false)]
  have s1 := dock_inH (Uniform.stepT true L 0 Rc Rc) sa sa_inj (by decide) B0 (by
    intro j
    fin_cases j
    · exact (ZeroPadding.pad_zero _).symm
    · rfl
    · rfl)
  let B1 := install sa B0 oa
  have B1_6 : B1 6 = ZeroPadding.pad Rc (false :: List.replicate (L+1) true) :=
    (install_slot sa sa_inj B0 oa 1).trans (pad_word_template (L+1) Rc (by omega))
  
  let ob : Fin 4 → List Bool := ![ZeroPadding.pad Rc (List.replicate M2 true),
    ZeroPadding.pad Rc (false :: List.replicate (L+1) true),
    ZeroPadding.pad Rc (List.replicate (M2*(L+1)) true),
    ZeroPadding.pad Rc (List.replicate (M2*(2*(L+1)+3)+2) false)]
  have s2 := dock_inH (stepHp M2 (L+1) Rc) sb sb_inj (by decide) B1 (by
    intro j
    fin_cases j
    · exact install_other sa B0 oa _ (by decide)
    · exact B1_6
    · exact install_other sa B0 oa _ (by decide)
    · exact install_other sa B0 oa _ (by decide))
  let B2 := install sb B1 ob
  
  let oc : Fin 4 → List Bool := ![ZeroPadding.pad Rc (List.replicate (M2*(L+1)) true),
    ZeroPadding.pad Rc (List.replicate U0 true),
    ZeroPadding.pad Rc (List.replicate (M2*(L+1)+U0) true),
    ZeroPadding.pad Rc (List.replicate (M2*(L+1)+U0+2) false)]
  have s3 := dock_inH (stepSp (M2*(L+1)) U0 Rc) sc sc_inj (by decide) B2 (by
    intro j
    fin_cases j
    · exact install_slot sb sb_inj B1 ob 2
    · exact (install_other sb B1 ob _ (by decide)).trans (install_other sa B0 oa _ (by decide))
    · exact (install_other sb B1 ob _ (by decide)).trans (install_other sa B0 oa _ (by decide))
    · exact (install_other sb B1 ob _ (by decide)).trans (install_other sa B0 oa _ (by decide)))
  let B3 := install sc B2 oc
  -- d: the rowWidth driver
  let od : Fin 3 → List Bool := ![ZeroPadding.pad Rc (List.replicate (rw M2 U0 L) true),
    ZeroPadding.pad Rc (UnaryTemplate.tape (rw M2 U0 L + false.toNat)),
    ZeroPadding.pad Rc (List.replicate (rw M2 U0 L+3) false)]
  have B3_10 : B3 10 = ZeroPadding.pad Rc (List.replicate (rw M2 U0 L) true) :=
    install_slot sc sc_inj B2 oc 2
  have s4 := dock_inH (Uniform.stepT false (rw M2 U0 L) Rc Rc Rc) sd sd_inj (by decide) B3 (by
    intro j
    fin_cases j
    · exact B3_10
    · exact (install_other sc B2 oc _ (by decide)).trans ((install_other sb B1 ob _ (by decide)).trans
        (install_other sa B0 oa _ (by decide)))
    · exact (install_other sc B2 oc _ (by decide)).trans ((install_other sb B1 ob _ (by decide)).trans
        (install_other sa B0 oa _ (by decide))))
  let B4 := install sd B3 od
  -- e: the counter head 1 → 0
  have s5 : Step (DecompositionCountPosition.move dirIn) 1 inH B4 (fun _ => 0) B4 :=
    (moveStep dirIn inH B4).congr (by
    funext i
    simp only [dirIn, inH]
    split_ifs <;> rfl) rfl
  -- f: 1^(rowWidth·N)
  let of : Fin 4 → List Bool := ![ZeroPadding.pad Rc (List.replicate (rw M2 U0 L) true),
    ZeroPadding.pad Rc (false :: List.replicate N true),
    ZeroPadding.pad Rc (List.replicate (rw M2 U0 L*N) true),
    ZeroPadding.pad Rc (List.replicate (rw M2 U0 L*(2*N+3)+2) false)]
  have B4_3 : B4 3 = ZeroPadding.pad Rc (false :: List.replicate N true) :=
    (install_other sd B3 od _ (by decide)).trans ((install_other sc B2 oc _ (by decide)).trans
      ((install_other sb B1 ob _ (by decide)).trans (install_other sa B0 oa _ (by decide))))
  have s6 := Dimension.dock0 (stepHp (rw M2 U0 L) N Rc) sf sf_inj B4 (by
    intro j
    fin_cases j
    · exact install_slot sd sd_inj B3 od 0
    · exact B4_3
    · exact (install_other sd B3 od _ (by decide)).trans ((install_other sc B2 oc _ (by decide)).trans
        ((install_other sb B1 ob _ (by decide)).trans (install_other sa B0 oa _ (by decide))))
    · exact (install_other sd B3 od _ (by decide)).trans ((install_other sc B2 oc _ (by decide)).trans
        ((install_other sb B1 ob _ (by decide)).trans (install_other sa B0 oa _ (by decide)))))
  let B5 := install sf B4 of
  -- g: the rowWidth·N driver
  let og : Fin 3 → List Bool := ![ZeroPadding.pad Rc (List.replicate (rw M2 U0 L * N) true),
    ZeroPadding.pad Rc (UnaryTemplate.tape (rw M2 U0 L * N + false.toNat)),
    ZeroPadding.pad Rc (List.replicate (rw M2 U0 L * N + 3) false)]
  have blank4 : ∀ i : Fin 16, (∀ j, sd j ≠ i) → (∀ j, sc j ≠ i) → (∀ j, sb j ≠ i) → (∀ j, sa j ≠ i) →
      4 ≤ i.val → B4 i = ZeroPadding.pad Rc [] := by
    intro i hd hc hb ha h4
    refine (install_other sd B3 od i hd).trans ((install_other sc B2 oc i hc).trans
      ((install_other sb B1 ob i hb).trans ((install_other sa B0 oa i ha).trans ?_)))
    simp only [B0, input, if_neg (show i.val ≠ 0 by omega), if_neg (show i.val ≠ 1 by omega),
      if_neg (show i.val ≠ 2 by omega), if_neg (show i.val ≠ 3 by omega)]
  have s7 := Dimension.dock0 (Uniform.stepT false (rw M2 U0 L * N) Rc Rc Rc) sg sg_inj B5 (by
    intro j
    fin_cases j
    · exact install_slot sf sf_inj B4 of 2
    · exact (install_other sf B4 of _ (by decide)).trans
        (blank4 5 (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact (install_other sf B4 of _ (by decide)).trans
        (blank4 15 (by decide) (by decide) (by decide) (by decide) (by decide)))
  let B6 := install sg B5 og
  -- h: counter and drivers to head 1
  have s8 : Step (DecompositionCountPosition.move dirOut) 1 (fun _ => 0) B6 outH B6 :=
    (moveStep dirOut (fun _ => 0) B6).congr (by
    funext i
    simp only [dirOut, outH]
    split_ifs <;> rfl) rfl
  refine ⟨B6, (((((((s1.seq s2).seq s3).seq s4).seq s5).seq s6).seq s7).seq s8), ?_, ?_, ?_⟩
  · refine (install_other sg B5 og _ (by decide)).trans ((install_other sf B4 of _ (by decide)).trans
      ((install_slot sd sd_inj B3 od 1).trans ?_))
    simp [od]
  · refine (install_slot sg sg_inj B5 og 1).trans ?_
    simp [og]
  · exact (install_other sg B5 og _ (by decide)).trans (install_slot sf sf_inj B4 of 1)

end
end NearCubicWires.SourceConstruction.RowWidth
end

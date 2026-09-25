import Proof.SourceAssembly.SourceCleanupClass

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding
open NearCubicWires.SupplierEstimator
namespace NearCubicWires.SourceConstruction.Dimension
noncomputable section

/-! ## 1. Zero-head docking -/

theorem dock0 {t u s n : ℕ} {p : Machine t s} {tin tout : Fin t → List Bool}
    (h : Step p n (fun _ => 0) tin (fun _ => 0) tout) (slots : Fin t → Fin u)
    (hi : Function.Injective slots) (A : Fin u → List Bool) (hA : ∀ j, A (slots j) = tin j) :
    Step (RecoveryFocus.machine slots p) n (fun _ => 0) A (fun _ => 0) (install slots A tout) := by
  have hs := h.dock slots hi (fun _ => 0) A (fun _ => rfl) hA
  rwa [BlockPlatform.dockH_existing slots (fun _ => 0) (fun _ => 0) (fun _ => rfl)] at hs

/-! ## 2. The local layout -/

/-- First free tape after the `hR` polynomial block: `Rc`'s output. -/
def o1 (hR : ℕ) : ℕ := 64 + 2*hR
/-- `V`'s output. -/
def o2 (hR hV : ℕ) : ℕ := o1 hR + 15 + 2*hV
/-- The local universe. -/
def P (hR hV : ℕ) : ℕ := o2 hR hV + 2

variable (hR hV : ℕ)

theorem P_ge : 66 ≤ P hR hV := by unfold P o2 o1; omega

def aV (i : ℕ) : ℕ := i
def lcV (j : ℕ) : ℕ := if j = 0 then 1 else 2 + j
def cV' (i : ℕ) : ℕ := if i = 0 then 0 else if i = 1 then 27 else if i = 2 then 29 else 30
def dV (i : ℕ) : ℕ := if i = 0 then 29 else if i = 1 then 31 else 32
def eV (j : ℕ) : ℕ := if j = 0 then 31 else 32 + j
def fV (i : ℕ) : ℕ := if i = 0 then 0 else if i = 1 then 49 else 50
def gV (j : ℕ) : ℕ := if j = 0 then 49 else 50 + j
def hVal (i : ℕ) : ℕ :=
  if i = 0 then 53 + 2*hR else if i = 1 then 45 else if i = 2 then o1 hR else o1 hR + 1
def iV (j : ℕ) : ℕ := if j = 0 then 49 else o1 hR + 1 + j
def jV (i : ℕ) : ℕ :=
  if i = 0 then o1 hR + 4 + 2*hV else if i = 1 then 45 else if i = 2 then o2 hR hV else o2 hR hV + 1

/-- Unfold the layout values and close an index (in)equality. -/
macro "lay" : tactic => `(tactic| (
  simp only [aV, lcV, cV', dV, eV, fV, gV, hVal, iV, jV, o1, o2, P,
    BlockPlatform.UnaryCalc.tapes, RepairSource.ProjectionNormalization.DimensionPolynomial.tapes] at *
  try split_ifs at *
  all_goals omega))

def aSl : Fin 3 → Fin (P hR hV) := fun i => ⟨aV i.val, by have := i.isLt; lay⟩
def lcSl : Fin 27 → Fin (P hR hV) := fun j => ⟨lcV j.val, by have := j.isLt; lay⟩
def cSl : Fin 4 → Fin (P hR hV) := fun i => ⟨cV' i.val, by have := i.isLt; lay⟩
def dSl : Fin 3 → Fin (P hR hV) := fun i => ⟨dV i.val, by have := i.isLt; lay⟩
def eSl : Fin 17 → Fin (P hR hV) := fun j => ⟨eV j.val, by have := j.isLt; lay⟩
def fSl : Fin 3 → Fin (P hR hV) := fun i => ⟨fV i.val, by have := i.isLt; lay⟩
def gSl : Fin (BlockPlatform.UnaryCalc.tapes hR) → Fin (P hR hV) :=
  fun j => ⟨gV j.val, by have := j.isLt; lay⟩
def hSl : Fin 4 → Fin (P hR hV) := fun i => ⟨hVal hR i.val, by have := i.isLt; lay⟩
def iSl : Fin (BlockPlatform.UnaryCalc.tapes hV) → Fin (P hR hV) :=
  fun j => ⟨iV hR j.val, by have := j.isLt; lay⟩
def jSl : Fin 4 → Fin (P hR hV) := fun i => ⟨jV hR hV i.val, by have := i.isLt; lay⟩

macro "injv" : tactic => `(tactic| (
  intro a b hab
  have hv := congrArg Fin.val hab
  have ha := a.isLt
  have hb := b.isLt
  simp only [aSl, lcSl, cSl, dSl, eSl, fSl, gSl, hSl, iSl, jSl] at hv
  apply Fin.ext
  lay))

theorem aSl_inj : Function.Injective (aSl hR hV) := by injv
theorem lcSl_inj : Function.Injective (lcSl hR hV) := by injv
theorem cSl_inj : Function.Injective (cSl hR hV) := by injv
theorem dSl_inj : Function.Injective (dSl hR hV) := by injv
theorem eSl_inj : Function.Injective (eSl hR hV) := by injv
theorem fSl_inj : Function.Injective (fSl hR hV) := by injv
theorem gSl_inj : Function.Injective (gSl hR hV) := by injv
theorem hSl_inj : Function.Injective (hSl hR hV) := by injv
theorem iSl_inj : Function.Injective (iSl hR hV) := by injv
theorem jSl_inj : Function.Injective (jSl hR hV) := by injv

/-! ## 3. The machine and its cost -/

/-- The cheap prefix: stages A-G and I (all `poly(q)` or `O(q·2^(q-K))`). -/
def prefixMachine (L C cVc : ℕ) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine (aSl hR hV) (UWalkUnary.machine true false))
    (RecoveryFocus.machine (lcSl hR hV) (PCJ6e421fabe2aa4155_SourceLiveCount.machine L)))
    (RecoveryFocus.machine (cSl hR hV) MatrixUnaryDifference.resetMachine))
    (RecoveryFocus.machine (dSl hR hV) (UWalkUnary.machine false false)))
    (RecoveryFocus.machine (eSl hR hV) RepairSource.CloseoutCapacity.Power.machine))
    (RecoveryFocus.machine (fSl hR hV) (UWalkUnary.machine false false)))
    (RecoveryFocus.machine (gSl hR hV) (PCPSerializerCapacity.Power.machine hR C)))
    (RecoveryFocus.machine (iSl hR hV) (PCPSerializerCapacity.Power.machine hV cVc))

/-- The whole pipeline: the cheap prefix, then the two exact products H (`Rc`) and J (`V`). -/
def machine (L C cVc : ℕ) :=
  Composition.machine (Composition.machine (prefixMachine hR hV L C cVc)
    (RecoveryFocus.machine (hSl hR hV) ClockUnaryProduct.machine))
    (RecoveryFocus.machine (jSl hR hV) ClockUnaryProduct.machine)

/-- The residual `q - K`. -/
abbrev res (L q : ℕ) : ℕ := q - normalizedLiveCount q L

/-- The prefix's cost: every stage but the two final products. -/
def prefixCost (L C cVc q : ℕ) : ℕ :=
  let r := res L q
  (((((((2*q+6)+1+PCJ6e421fabe2aa4155_SourceLiveCount.budget q L)+1+(2*q+8))+1+(2*r+6))+1+
    RepairSource.CloseoutCapacity.Power.budget r)+1+(2*q+6))+1+PCPSerializerCapacity.Power.budget hR C q)+1+
    PCPSerializerCapacity.Power.budget hV cVc q

def cost (L C cVc q : ℕ) : ℕ :=
  let r := res L q
  (prefixCost hR hV L C cVc q+1+(2*((C*(q+1)^hR)*(2*2^r+3)+2)+2))+1+
    (2*((cVc*(q+1)^hV)*(2*2^r+3)+2)+2)

/-- The input: the arity template on tape 0, everything else blank. -/
def input (q : ℕ) : Fin (P hR hV) → List Bool := fun i => if i.val = 0 then UnaryTemplate.tape q else []

/-! ## 4. The ten stages, each an exact `Step` on its own tapes (heads `0` in and out) -/

theorem stepA (q : ℕ) : Step (UWalkUnary.machine true false) (2*q+6) (fun _ => 0)
    ![UnaryTemplate.tape q, [], []] (fun _ => 0)
    ![UnaryTemplate.tape q, CompareMachine.word q, List.replicate (q+2) false] := by
  have h := CloseoutFinalSelector.step_of_clock (UWalkUnary.ready true false (q+2) q)
  refine (h.congr_in rfl ?_).congr rfl ?_
  · funext i; fin_cases i <;>
      simp [UWalkUnary.input, RepairSource.CloseoutCapacity.Power.template_source]
  · funext i; fin_cases i <;>
      simp [UWalkUnary.result, UWalkUnary.output, UWalkUnary.lead, CompareMachine.word,
        RepairSource.CloseoutCapacity.Power.template_source]

theorem stepU (n : ℕ) : Step (UWalkUnary.machine false false) (2*n+6) (fun _ => 0)
    ![UnaryTemplate.tape n, [], []] (fun _ => 0)
    ![UnaryTemplate.tape n, List.replicate n true, List.replicate (n+2) false] := by
  have h := CloseoutFinalSelector.step_of_clock (UWalkUnary.ready false false (n+2) n)
  refine (h.congr_in rfl ?_).congr rfl ?_
  · funext i; fin_cases i <;>
      simp [UWalkUnary.input, RepairSource.CloseoutCapacity.Power.template_source]
  · funext i; fin_cases i <;>
      simp [UWalkUnary.result, UWalkUnary.output, UWalkUnary.lead,
        RepairSource.CloseoutCapacity.Power.template_source]

theorem lc_input (q : ℕ) (j : Fin 27) :
    PCJ6e421fabe2aa4155_SourceLiveCount.input q j = if j.val = 0 then CompareMachine.word q else [] := by
  refine Fin.addCases (m := 16) (n := 11) (fun i => ?_) (fun i => ?_) j
  · simp only [PCJ6e421fabe2aa4155_SourceLiveCount.input, Fin.addCases_left,
      PCJ6e421fabe2aa4155_SourceLog.input, Fin.val_castAdd]
    by_cases hi : i.val = 0
    · have : i = 0 := Fin.ext hi
      simp [this]
    · simp [hi, show i ≠ 0 from fun h => hi (by rw [h]; rfl)]
  · simp only [PCJ6e421fabe2aa4155_SourceLiveCount.input, Fin.addCases_right, Fin.val_natAdd]
    simp

theorem stepB (q L : ℕ) : ∃ W : Fin 27 → List Bool,
    Step (PCJ6e421fabe2aa4155_SourceLiveCount.machine L) (PCJ6e421fabe2aa4155_SourceLiveCount.budget q L)
      (fun _ => 0) (fun j => if j.val = 0 then CompareMachine.word q else []) (fun _ => 0) W ∧
    W 25 = UnaryTemplate.tape (normalizedLiveCount q L) := by
  obtain ⟨W, h, _, h25⟩ := PCJ6e421fabe2aa4155_SourceLiveCount.run q L
  exact ⟨W, h.congr_in rfl (funext (lc_input q)), h25⟩

theorem stepC (q K : ℕ) (hK : K ≤ q) : ∃ W : Fin 4 → List Bool,
    Step MatrixUnaryDifference.resetMachine (2*q+8) (fun _ => 0)
      ![UnaryTemplate.tape q, UnaryTemplate.tape K, [], []] (fun _ => 0) W ∧
    W 0 = UnaryTemplate.tape q ∧ W 1 = UnaryTemplate.tape K ∧ W 2 = UnaryTemplate.tape (q-K) := by
  obtain ⟨r, hr, h0, h1, h2, hh, hs⟩ := MatrixUnaryDifference.reset_run q K hK
  refine ⟨r.final.tapes, ?_, h0, h1, h2⟩
  have hin : MatrixUnaryDifference.resetInput q K = ![UnaryTemplate.tape q, UnaryTemplate.tape K, [], []] := by
    funext i; fin_cases i <;> rfl
  rw [hin] at hr
  exact ⟨r, hr, funext hh, rfl, le_of_eq hs⟩

theorem stepE (d : ℕ) : ∃ W : Fin 17 → List Bool,
    Step RepairSource.CloseoutCapacity.Power.machine (RepairSource.CloseoutCapacity.Power.budget d)
      (fun _ => 0) (fun i => if i.val = 0 then List.replicate d true else []) (fun _ => 0) W ∧
    W 15 = List.replicate (2^d) true ∧ W 13 = UnaryTemplate.tape (2^d) := by
  obtain ⟨W, h, h15, h13⟩ := RepairSource.CloseoutCapacity.Power.power_run d
  exact ⟨W, CloseoutFinalSelector.step_of_clock h, h15, h13⟩

theorem stepG (D C q : ℕ) : ∃ W : Fin (BlockPlatform.UnaryCalc.tapes D) → List Bool,
    Step (PCPSerializerCapacity.Power.machine D C) (PCPSerializerCapacity.Power.budget D C q)
      (fun _ => 0) (fun i => if i.val = 0 then List.replicate q true else []) (fun _ => 0) W ∧
    W ⟨0, by simp [BlockPlatform.UnaryCalc.tapes, RepairSource.ProjectionNormalization.DimensionPolynomial.tapes]⟩ =
      List.replicate q true ∧
    W ⟨3+2*D, by simp [BlockPlatform.UnaryCalc.tapes, RepairSource.ProjectionNormalization.DimensionPolynomial.tapes]⟩ =
      List.replicate (C*(q+1)^D) true := by
  obtain ⟨W, h, h0, h1⟩ := BlockPlatform.UnaryCalc.poly_step D C q
  exact ⟨W, h, h0, h1⟩

theorem stepH (d e : ℕ) : Step ClockUnaryProduct.machine (2*(d*(2*e+3)+2)+2) (fun _ => 0)
    ![List.replicate d true, UnaryTemplate.tape e, [], []] (fun _ => 0)
    ![List.replicate d true, UnaryTemplate.tape e, List.replicate (d*e) true,
      List.replicate (d*(2*e+3)+2) false] := by
  have h := (BlockPlatform.UnaryCalc.product_step d e).pad (fun i => if i.val = 1 then e+2 else 0)
  have ht : ZeroPadding.pad (e+2) (false :: List.replicate e true) = UnaryTemplate.tape e := by
    simp [ZeroPadding.pad, UnaryTemplate.tape]
  refine (h.congr_in rfl ?_).congr rfl ?_
  · funext i
    fin_cases i
    · exact ZeroPadding.pad_zero _
    · exact ht
    · exact ZeroPadding.pad_zero _
    · exact ZeroPadding.pad_zero _
  · funext i
    fin_cases i
    · exact ZeroPadding.pad_zero _
    · exact ht
    · exact ZeroPadding.pad_zero _
    · exact ZeroPadding.pad_zero _

/-! ## 5. Bookkeeping: where each stage writes -/

theorem at_slot {t u : ℕ} (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (A : Fin u → List Bool) (loc : Fin t → List Bool) (j : Fin t) (x : Fin u)
    (hx : (slots j).val = x.val) : install slots A loc x = loc j := by
  rw [← Fin.ext hx]
  exact install_slot slots hi A loc j

theorem off_slot {t u : ℕ} (slots : Fin t → Fin u) (A : Fin u → List Bool) (loc : Fin t → List Bool)
    (x : Fin u) (hx : ∀ j, (slots j).val ≠ x.val) : install slots A loc x = A x :=
  install_other slots A loc x (fun j h => hx j (congrArg Fin.val h))

/-- A stage whose slots lie below `k` leaves every tape at or above `k` as it was. -/
theorem fresh_step {t u : ℕ} (slots : Fin t → Fin u) (A : Fin u → List Bool)
    (loc : Fin t → List Bool) (k0 k : ℕ) (hk : k0 ≤ k) (hsl : ∀ j, (slots j).val < k)
    (hA : ∀ x : Fin u, k0 ≤ x.val → A x = []) :
    ∀ x : Fin u, k ≤ x.val → install slots A loc x = [] := by
  intro x hx
  rw [off_slot slots A loc x (fun j => by have := hsl j; omega)]
  exact hA x (by omega)

macro "slv" : tactic => `(tactic| (
  intro j
  have hj := j.isLt
  simp only [aSl, lcSl, cSl, dSl, eSl, fSl, gSl, hSl, iSl, jSl] at *
  lay))

theorem aSl_lt : ∀ j, (aSl hR hV j).val < 3 := by slv
theorem lcSl_lt : ∀ j, (lcSl hR hV j).val < 29 := by slv
theorem cSl_lt : ∀ j, (cSl hR hV j).val < 31 := by slv
theorem dSl_lt : ∀ j, (dSl hR hV j).val < 33 := by slv
theorem eSl_lt : ∀ j, (eSl hR hV j).val < 49 := by slv
theorem fSl_lt : ∀ j, (fSl hR hV j).val < 51 := by slv
theorem gSl_lt : ∀ j, (gSl hR hV j).val < o1 hR := by slv
theorem hSl_lt : ∀ j, (hSl hR hV j).val < o1 hR + 2 := by slv
theorem iSl_lt : ∀ j, (iSl hR hV j).val < o2 hR hV := by slv

theorem lcSl_ne0 : ∀ j, (lcSl hR hV j).val ≠ 0 := by slv
theorem dSl_ne0 : ∀ j, (dSl hR hV j).val ≠ 0 := by slv
theorem eSl_ne0 : ∀ j, (eSl hR hV j).val ≠ 0 := by slv
theorem fSl_ne45 : ∀ j, (fSl hR hV j).val ≠ 45 := by slv
theorem gSl_ne0 : ∀ j, (gSl hR hV j).val ≠ 0 := by slv
theorem gSl_ne45 : ∀ j, (gSl hR hV j).val ≠ 45 := by slv
theorem hSl_ne0 : ∀ j, (hSl hR hV j).val ≠ 0 := by slv
theorem hSl_ne49 : ∀ j, (hSl hR hV j).val ≠ 49 := by slv
theorem iSl_ne0 : ∀ j, (iSl hR hV j).val ≠ 0 := by slv
theorem iSl_ne45 : ∀ j, (iSl hR hV j).val ≠ 45 := by slv
theorem iSl_neR : ∀ j, (iSl hR hV j).val ≠ o1 hR := by slv
theorem iSl_neRl : ∀ j, (iSl hR hV j).val ≠ o1 hR + 1 := by slv
theorem jSl_ne0 : ∀ j, (jSl hR hV j).val ≠ 0 := by slv
theorem iSl_ne_d : ∀ j, (iSl hR hV j).val ≠ 53 + 2*hR := by slv
theorem jSl_ne_d : ∀ j, (jSl hR hV j).val ≠ 53 + 2*hR := by slv
theorem hSl_ne_dV : ∀ j, (hSl hR hV j).val ≠ o1 hR + 4 + 2*hV := by slv
theorem jSl_ne49 : ∀ j, (jSl hR hV j).val ≠ 49 := by slv
theorem jSl_neR : ∀ j, (jSl hR hV j).val ≠ o1 hR := by slv
theorem jSl_neRl : ∀ j, (jSl hR hV j).val ≠ o1 hR + 1 := by slv

/-! ## 6. The named outputs -/

def pq : Fin (P hR hV) := ⟨0, by unfold P o2 o1; omega⟩
def pE : Fin (P hR hV) := ⟨45, by unfold P o2 o1; omega⟩
def pRep : Fin (P hR hV) := ⟨49, by unfold P o2 o1; omega⟩
def pR : Fin (P hR hV) := ⟨o1 hR, by unfold P o2; omega⟩
def pRl : Fin (P hR hV) := ⟨o1 hR + 1, by unfold P o2; omega⟩
def pV : Fin (P hR hV) := ⟨o2 hR hV, by unfold P; omega⟩
def pVl : Fin (P hR hV) := ⟨o2 hR hV + 1, by unfold P; omega⟩

/-! ## 7. The pipeline run -/

/-- **The one-time capacity pipeline.** From the resident arity template (tape `pq`, everything
else blank, heads `0`) the fixed machine reaches, heads `0`:
- `Rc = C·tableClass L hR q` on `pR`, with its exact product log on `pRl`;
- `V = cVc·tableClass L hV q` on `pV`, with its log on `pVl`;
- the arity unchanged on `pq`;
- `1^q` on `pRep` and `tape (2^(q-K))` on `pE`, both reusable.

Every other tape is existential, but its length is bounded by the cheap PREFIX's cost alone
(`q + 2 + prefixCost + 1`): the two products write only their exact tapes. So once
`prefixCost + q + 3 ≤ Rc`, the pipeline's whole workspace except the four exact product tapes can be
erased with the driver `Rc`. -/
theorem pipeline (L C cVc q : ℕ) : ∃ W : Fin (P hR hV) → List Bool,
    Step (machine hR hV L C cVc) (cost hR hV L C cVc q) (fun _ => 0) (input hR hV q) (fun _ => 0) W ∧
    W (pq hR hV) = UnaryTemplate.tape q ∧
    W (pE hR hV) = UnaryTemplate.tape (2^(q - normalizedLiveCount q L)) ∧
    W (pRep hR hV) = List.replicate q true ∧
    W (pR hR hV) = List.replicate (C * RuntimeShape.tableClass L hR q) true ∧
    W (pRl hR hV) =
      List.replicate (C*(q+1)^hR*(2*2^(q - normalizedLiveCount q L)+3)+2) false ∧
    W (pV hR hV) = List.replicate (cVc * RuntimeShape.tableClass L hV q) true ∧
    W (pVl hR hV) =
      List.replicate (cVc*(q+1)^hV*(2*2^(q - normalizedLiveCount q L)+3)+2) false ∧
    (∀ x : Fin (P hR hV), x ≠ pR hR hV → x ≠ pRl hR hV → x ≠ pV hR hV → x ≠ pVl hR hV →
      (W x).length ≤ q + 2 + prefixCost hR hV L C cVc q + 1) := by
  have hK : normalizedLiveCount q L ≤ q := normalizedLiveCount_le q L
  -- A: word q
  let oA : Fin 3 → List Bool := ![UnaryTemplate.tape q, CompareMachine.word q, List.replicate (q+2) false]
  have sA := dock0 (stepA q) (aSl hR hV) (aSl_inj hR hV) (input hR hV q) (by
    intro j
    fin_cases j <;> simp [aSl, aV, input])
  let B1 := install (aSl hR hV) (input hR hV q) oA
  have B1q : B1 (pq hR hV) = UnaryTemplate.tape q := at_slot _ (aSl_inj hR hV) _ _ 0 _ rfl
  have B1w : B1 ⟨1, by unfold P o2 o1; omega⟩ = CompareMachine.word q :=
    at_slot _ (aSl_inj hR hV) _ _ 1 _ rfl
  have B1f : ∀ x : Fin (P hR hV), 3 ≤ x.val → B1 x = [] := fresh_step (aSl hR hV) (input hR hV q)
    oA 1 3 (by omega) (aSl_lt hR hV) (fun x hx => by simp only [input]; rw [if_neg (by omega)])
  -- B: tape K
  obtain ⟨WB, hBs, hB25⟩ := stepB q L
  have sB := dock0 hBs (lcSl hR hV) (lcSl_inj hR hV) B1 (by
    intro j
    by_cases hj : j.val = 0
    · rw [if_pos hj, ← B1w]
      congr 1
      exact Fin.ext (by simp [lcSl, lcV, hj])
    · rw [if_neg hj]
      exact B1f _ (by simp [lcSl, lcV, hj]; omega))
  let B2 := install (lcSl hR hV) B1 WB
  have B2q : B2 (pq hR hV) = UnaryTemplate.tape q :=
    (off_slot (lcSl hR hV) B1 WB (pq hR hV) (lcSl_ne0 hR hV)).trans B1q
  have B2K : B2 ⟨27, by unfold P o2 o1; omega⟩ = UnaryTemplate.tape (normalizedLiveCount q L) :=
    (at_slot _ (lcSl_inj hR hV) B1 WB 25 _ rfl).trans hB25
  have B2f : ∀ x : Fin (P hR hV), 29 ≤ x.val → B2 x = [] :=
    fresh_step (lcSl hR hV) B1 WB 3 29 (by omega) (lcSl_lt hR hV) B1f
  -- C: tape (q-K)
  obtain ⟨WC, hCs, hC0, _, hC2⟩ := stepC q (normalizedLiveCount q L) hK
  have sC := dock0 hCs (cSl hR hV) (cSl_inj hR hV) B2 (by
    intro j
    fin_cases j
    · exact B2q
    · exact B2K
    · exact B2f _ (by simp [cSl, cV'])
    · exact B2f _ (by simp [cSl, cV']))
  let B3 := install (cSl hR hV) B2 WC
  have B3q : B3 (pq hR hV) = UnaryTemplate.tape q :=
    (at_slot (cSl hR hV) (cSl_inj hR hV) B2 WC 0 (pq hR hV) rfl).trans hC0
  have B3r : B3 ⟨29, by unfold P o2 o1; omega⟩ = UnaryTemplate.tape (q - normalizedLiveCount q L) :=
    (at_slot _ (cSl_inj hR hV) B2 WC 2 _ rfl).trans hC2
  have B3f : ∀ x : Fin (P hR hV), 31 ≤ x.val → B3 x = [] :=
    fresh_step (cSl hR hV) B2 WC 29 31 (by omega) (cSl_lt hR hV) B2f
  -- D: 1^(q-K)
  let oD : Fin 3 → List Bool := ![UnaryTemplate.tape (q - normalizedLiveCount q L),
    List.replicate (q - normalizedLiveCount q L) true, List.replicate (q - normalizedLiveCount q L + 2) false]
  have sD := dock0 (stepU (q - normalizedLiveCount q L)) (dSl hR hV) (dSl_inj hR hV) B3 (by
    intro j
    fin_cases j
    · exact B3r
    · exact B3f _ (by simp [dSl, dV])
    · exact B3f _ (by simp [dSl, dV]))
  let B4 := install (dSl hR hV) B3 oD
  have B4q : B4 (pq hR hV) = UnaryTemplate.tape q :=
    (off_slot (dSl hR hV) B3 oD (pq hR hV) (dSl_ne0 hR hV)).trans B3q
  have B4r : B4 ⟨31, by unfold P o2 o1; omega⟩ = List.replicate (q - normalizedLiveCount q L) true :=
    at_slot _ (dSl_inj hR hV) B3 oD 1 _ rfl
  have B4f : ∀ x : Fin (P hR hV), 33 ≤ x.val → B4 x = [] :=
    fresh_step (dSl hR hV) B3 oD 31 33 (by omega) (dSl_lt hR hV) B3f
  -- E: 2^(q-K)
  obtain ⟨WE, hEs, _, hE13⟩ := stepE (q - normalizedLiveCount q L)
  have sE := dock0 hEs (eSl hR hV) (eSl_inj hR hV) B4 (by
    intro j
    by_cases hj : j.val = 0
    · rw [if_pos hj, ← B4r]
      congr 1
      exact Fin.ext (by simp [eSl, eV, hj])
    · rw [if_neg hj]
      exact B4f _ (by simp [eSl, eV, hj]; omega))
  let B5 := install (eSl hR hV) B4 WE
  have B5q : B5 (pq hR hV) = UnaryTemplate.tape q :=
    (off_slot (eSl hR hV) B4 WE (pq hR hV) (eSl_ne0 hR hV)).trans B4q
  have B5E : B5 (pE hR hV) = UnaryTemplate.tape (2^(q - normalizedLiveCount q L)) :=
    (at_slot (eSl hR hV) (eSl_inj hR hV) B4 WE 13 (pE hR hV) rfl).trans hE13
  have B5f : ∀ x : Fin (P hR hV), 49 ≤ x.val → B5 x = [] :=
    fresh_step (eSl hR hV) B4 WE 33 49 (by omega) (eSl_lt hR hV) B4f
  -- F: 1^q
  let oF : Fin 3 → List Bool := ![UnaryTemplate.tape q, List.replicate q true, List.replicate (q+2) false]
  have sF := dock0 (stepU q) (fSl hR hV) (fSl_inj hR hV) B5 (by
    intro j
    fin_cases j
    · exact B5q
    · exact B5f _ (by simp [fSl, fV])
    · exact B5f _ (by simp [fSl, fV]))
  let B6 := install (fSl hR hV) B5 oF
  have B6q : B6 (pq hR hV) = UnaryTemplate.tape q := at_slot (fSl hR hV) (fSl_inj hR hV) B5 oF 0 _ rfl
  have B6rep : B6 (pRep hR hV) = List.replicate q true := at_slot (fSl hR hV) (fSl_inj hR hV) B5 oF 1 _ rfl
  have B6E : B6 (pE hR hV) = UnaryTemplate.tape (2^(q - normalizedLiveCount q L)) :=
    (off_slot (fSl hR hV) B5 oF (pE hR hV) (fSl_ne45 hR hV)).trans B5E
  have B6f : ∀ x : Fin (P hR hV), 51 ≤ x.val → B6 x = [] :=
    fresh_step (fSl hR hV) B5 oF 49 51 (by omega) (fSl_lt hR hV) B5f
  -- G: 1^(C(q+1)^hR)
  obtain ⟨WG, hGs, hG0, hG1⟩ := stepG hR C q
  have sG := dock0 hGs (gSl hR hV) (gSl_inj hR hV) B6 (by
    intro j
    by_cases hj : j.val = 0
    · rw [if_pos hj, ← B6rep]
      congr 1
      exact Fin.ext (by simp [gSl, gV, hj, pRep])
    · rw [if_neg hj]
      exact B6f _ (by simp [gSl, gV, hj]; omega))
  let B7 := install (gSl hR hV) B6 WG
  have B7q : B7 (pq hR hV) = UnaryTemplate.tape q :=
    (off_slot (gSl hR hV) B6 WG (pq hR hV) (gSl_ne0 hR hV)).trans B6q
  have B7E : B7 (pE hR hV) = UnaryTemplate.tape (2^(q - normalizedLiveCount q L)) :=
    (off_slot (gSl hR hV) B6 WG (pE hR hV) (gSl_ne45 hR hV)).trans B6E
  have B7rep : B7 (pRep hR hV) = List.replicate q true :=
    (at_slot (gSl hR hV) (gSl_inj hR hV) B6 WG _ (pRep hR hV) rfl).trans hG0
  have B7d : B7 ⟨53 + 2*hR, by unfold P o2 o1; omega⟩ = List.replicate (C*(q+1)^hR) true :=
    (at_slot (gSl hR hV) (gSl_inj hR hV) B6 WG _ _ (by simp [gSl, gV]; omega)).trans hG1
  have B7f : ∀ x : Fin (P hR hV), o1 hR ≤ x.val → B7 x = [] :=
    fresh_step (gSl hR hV) B6 WG 51 (o1 hR) (by unfold o1; omega) (gSl_lt hR hV) B6f
  -- I: 1^(cVc(q+1)^hV)
  obtain ⟨WI, hIs, hI0, hI1⟩ := stepG hV cVc q
  have sI := dock0 hIs (iSl hR hV) (iSl_inj hR hV) B7 (by
    intro j
    by_cases hj : j.val = 0
    · rw [if_pos hj, ← B7rep]
      congr 1
      exact Fin.ext (by simp [iSl, iV, hj, pRep])
    · rw [if_neg hj]
      exact B7f _ (by simp [iSl, iV, hj]; omega))
  let B8 := install (iSl hR hV) B7 WI
  have B8q : B8 (pq hR hV) = UnaryTemplate.tape q :=
    (off_slot (iSl hR hV) B7 WI (pq hR hV) (iSl_ne0 hR hV)).trans B7q
  have B8E : B8 (pE hR hV) = UnaryTemplate.tape (2^(q - normalizedLiveCount q L)) :=
    (off_slot (iSl hR hV) B7 WI (pE hR hV) (iSl_ne45 hR hV)).trans B7E
  have B8rep : B8 (pRep hR hV) = List.replicate q true :=
    (at_slot (iSl hR hV) (iSl_inj hR hV) B7 WI _ (pRep hR hV) rfl).trans hI0
  have B8d : B8 ⟨53 + 2*hR, by unfold P o2 o1; omega⟩ = List.replicate (C*(q+1)^hR) true :=
    (off_slot (iSl hR hV) B7 WI _ (iSl_ne_d hR hV)).trans B7d
  have B8dV : B8 ⟨o1 hR + 4 + 2*hV, by unfold P o2; omega⟩ = List.replicate (cVc*(q+1)^hV) true :=
    (at_slot (iSl hR hV) (iSl_inj hR hV) B7 WI _ _ (by simp [iSl, iV]; omega)).trans hI1
  have B8R : B8 (pR hR hV) = [] :=
    (off_slot (iSl hR hV) B7 WI (pR hR hV) (iSl_neR hR hV)).trans (B7f _ (by simp [pR]))
  have B8Rl : B8 (pRl hR hV) = [] :=
    (off_slot (iSl hR hV) B7 WI (pRl hR hV) (iSl_neRl hR hV)).trans (B7f _ (by simp [pRl]))
  have B8f : ∀ x : Fin (P hR hV), o2 hR hV ≤ x.val → B8 x = [] :=
    fresh_step (iSl hR hV) B7 WI (o1 hR) (o2 hR hV) (by unfold o2; omega) (iSl_lt hR hV) B7f
  -- H: Rc
  let oH : Fin 4 → List Bool := ![List.replicate (C*(q+1)^hR) true,
    UnaryTemplate.tape (2^(q - normalizedLiveCount q L)),
    List.replicate (C*(q+1)^hR*2^(q - normalizedLiveCount q L)) true,
    List.replicate (C*(q+1)^hR*(2*2^(q - normalizedLiveCount q L)+3)+2) false]
  have sH := dock0 (stepH (C*(q+1)^hR) (2^(q - normalizedLiveCount q L))) (hSl hR hV)
    (hSl_inj hR hV) B8 (by
    intro j
    fin_cases j
    · exact B8d
    · exact B8E
    · exact B8R
    · exact B8Rl)
  let B9 := install (hSl hR hV) B8 oH
  have B9q : B9 (pq hR hV) = UnaryTemplate.tape q :=
    (off_slot (hSl hR hV) B8 oH (pq hR hV) (hSl_ne0 hR hV)).trans B8q
  have B9E : B9 (pE hR hV) = UnaryTemplate.tape (2^(q - normalizedLiveCount q L)) :=
    at_slot (hSl hR hV) (hSl_inj hR hV) B8 oH 1 _ rfl
  have B9rep : B9 (pRep hR hV) = List.replicate q true :=
    (off_slot (hSl hR hV) B8 oH (pRep hR hV) (hSl_ne49 hR hV)).trans B8rep
  have B9R : B9 (pR hR hV) = List.replicate (C*(q+1)^hR*2^(q - normalizedLiveCount q L)) true :=
    at_slot (hSl hR hV) (hSl_inj hR hV) B8 oH 2 _ (by simp [hSl, hVal, pR])
  have B9Rl : B9 (pRl hR hV) =
      List.replicate (C*(q+1)^hR*(2*2^(q - normalizedLiveCount q L)+3)+2) false :=
    at_slot (hSl hR hV) (hSl_inj hR hV) B8 oH 3 _ (by simp [hSl, hVal, pRl])
  have B9d : B9 ⟨o1 hR + 4 + 2*hV, by unfold P o2; omega⟩ = List.replicate (cVc*(q+1)^hV) true :=
    (off_slot (hSl hR hV) B8 oH _ (hSl_ne_dV hR hV)).trans B8dV
  have B9f : ∀ x : Fin (P hR hV), o2 hR hV ≤ x.val → B9 x = [] :=
    fresh_step (hSl hR hV) B8 oH (o2 hR hV) (o2 hR hV) le_rfl
      (fun j => lt_of_lt_of_le (hSl_lt hR hV j) (by unfold o2; omega)) B8f
  -- J: V
  let oJ : Fin 4 → List Bool := ![List.replicate (cVc*(q+1)^hV) true,
    UnaryTemplate.tape (2^(q - normalizedLiveCount q L)),
    List.replicate (cVc*(q+1)^hV*2^(q - normalizedLiveCount q L)) true,
    List.replicate (cVc*(q+1)^hV*(2*2^(q - normalizedLiveCount q L)+3)+2) false]
  have sJ := dock0 (stepH (cVc*(q+1)^hV) (2^(q - normalizedLiveCount q L))) (jSl hR hV)
    (jSl_inj hR hV) B9 (by
    intro j
    fin_cases j
    · exact B9d
    · exact B9E
    · exact B9f _ (by simp [jSl, jV])
    · exact B9f _ (by simp [jSl, jV]))
  let B10 := install (jSl hR hV) B9 oJ
  have sPre : Step (prefixMachine hR hV L C cVc) (prefixCost hR hV L C cVc q) (fun _ => 0)
      (input hR hV q) (fun _ => 0) B8 :=
    ((((((sA.seq sB).seq sC).seq sD).seq sE).seq sF).seq sG).seq sI
  refine ⟨B10, (sPre.seq sH).seq sJ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (off_slot (jSl hR hV) B9 oJ (pq hR hV) (jSl_ne0 hR hV)).trans B9q
  · exact at_slot (jSl hR hV) (jSl_inj hR hV) B9 oJ 1 _ rfl
  · exact (off_slot (jSl hR hV) B9 oJ (pRep hR hV) (jSl_ne49 hR hV)).trans B9rep
  · have e : B10 (pR hR hV) = List.replicate (C*(q+1)^hR*2^(q - normalizedLiveCount q L)) true :=
      (off_slot (jSl hR hV) B9 oJ (pR hR hV) (jSl_neR hR hV)).trans B9R
    rw [e]
    simp only [RuntimeShape.tableClass, Nat.mul_assoc]
  · exact (off_slot (jSl hR hV) B9 oJ (pRl hR hV) (jSl_neRl hR hV)).trans B9Rl
  · have e : B10 (pV hR hV) = oJ 2 :=
      at_slot (jSl hR hV) (jSl_inj hR hV) B9 oJ 2 (pV hR hV) (by simp [jSl, jV, pV])
    rw [e]
    show List.replicate (cVc*(q+1)^hV*2^(q - normalizedLiveCount q L)) true = _
    simp only [RuntimeShape.tableClass, Nat.mul_assoc]
  · exact at_slot (jSl hR hV) (jSl_inj hR hV) B9 oJ 3 _ (by simp [jSl, jV, pVl])
  · intro x hxR hxRl hxV hxVl
    have vR : x.val ≠ o1 hR := fun h => hxR (Fin.ext h)
    have vRl : x.val ≠ o1 hR + 1 := fun h => hxRl (Fin.ext h)
    have vV : x.val ≠ o2 hR hV := fun h => hxV (Fin.ext h)
    have vVl : x.val ≠ o2 hR hV + 1 := fun h => hxVl (Fin.ext h)
    have hsame : B10 x = B8 x := by
      by_cases h45 : x.val = 45
      · have hx : x = pE hR hV := Fin.ext h45
        subst hx
        exact (at_slot (jSl hR hV) (jSl_inj hR hV) B9 oJ 1 _ rfl).trans B8E.symm
      by_cases hd : x.val = 53 + 2*hR
      · have hx : x = ⟨53 + 2*hR, by unfold P o2 o1; omega⟩ := Fin.ext hd
        rw [hx]
        exact ((off_slot (jSl hR hV) B9 oJ _ (jSl_ne_d hR hV)).trans
          (at_slot (hSl hR hV) (hSl_inj hR hV) B8 oH 0 _ rfl)).trans B8d.symm
      by_cases hdV : x.val = o1 hR + 4 + 2*hV
      · have hx : x = ⟨o1 hR + 4 + 2*hV, by unfold P o2; omega⟩ := Fin.ext hdV
        rw [hx]
        exact (at_slot (jSl hR hV) (jSl_inj hR hV) B9 oJ 0 _ rfl).trans B8dV.symm
      have oj : ∀ j, (jSl hR hV j).val ≠ x.val := by
        intro j
        have hj := j.isLt
        simp only [jSl, jV]
        split_ifs <;> omega
      have oh : ∀ j, (hSl hR hV j).val ≠ x.val := by
        intro j
        have hj := j.isLt
        simp only [hSl, hVal]
        split_ifs <;> omega
      exact (off_slot (jSl hR hV) B9 oJ x oj).trans (off_slot (hSl hR hV) B8 oH x oh)
    rw [hsame]
    have hd := (dirty_bound sPre x).1
    have hin : (input hR hV q x).length ≤ q + 2 := by
      simp only [input]
      split_ifs <;> simp [UnaryTemplate.tape]
    omega

/-! ## 8. Budget class, and the erasure condition -/

theorem liveCount_poly (q L : ℕ) :
    PCJ6e421fabe2aa4155_SourceLiveCount.budget q L ≤ (400 + 20*L) * (q+1)^2 := by
  simp only [PCJ6e421fabe2aa4155_SourceLiveCount.budget, PCJ6e421fabe2aa4155_SourceLog.budget,
    RepairSource.CloseoutSchedule.Clog.budget]
  have hlg := SourceConstruction.logScale_le q
  have hK := normalizedLiveCount_le q L
  have hm : L * logScale q ≤ L * (q+1) := Nat.mul_le_mul_left L hlg
  have hq : q + 1 ≤ (q+1)^2 := Nat.le_self_pow (by decide) _
  have hLq : L * (q+1) ≤ L * (q+1)^2 := Nat.mul_le_mul_left L hq
  have hL : L ≤ L * (q+1)^2 := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (Nat.succ_pos q))
  have e : q + 2 - 1 = q + 1 := by omega
  rw [e]
  have e2 : (400 + 20*L) * (q+1)^2 = 400*(q+1)^2 + 20*(L*(q+1)^2) := by ring
  have e3 : L * (2 * logScale q + 3) = 2*(L*logScale q) + 3*L := by ring
  rw [e2, e3]
  have e4 : (q+1)^2 = q*q + 2*q + 1 := by ring
  rw [e4] at hq hLq hL ⊢
  nlinarith

/-- The prefix cost in two pieces: a polynomial of degree `hR+1` and ONE table `(q+1)·2^(q-K)`. -/
theorem prefixCost_split (L C cVc q : ℕ) (h2 : 2 ≤ hR) (hVR : hV + 1 ≤ hR) :
    q + 3 + prefixCost hR hV L C cVc q ≤
      (450 + 20*L + BlockPlatform.UnaryCalc.polyCoefficient hR C +
        BlockPlatform.UnaryCalc.polyCoefficient hV cVc) * (q+1)^(hR+1) +
      300 * ((q+1) * 2^(q - normalizedLiveCount q L)) := by
  have hlc := liveCount_poly q L
  have hpw := SourceConstruction.power_class L q
  simp only [RuntimeShape.tableClass, pow_one] at hpw
  have hpR := BlockPlatform.UnaryCalc.poly_cost_polyBounded hR C q
  have hpV := BlockPlatform.UnaryCalc.poly_cost_polyBounded hV cVc q
  unfold ValidatorPolynomialDomination.PolyBounded at hpR hpV
  have hK := normalizedLiveCount_le q L
  have y1 : q + 1 ≤ (q+1)^(hR+1) := Nat.le_self_pow (by omega) _
  have y2 : (q+1)^2 ≤ (q+1)^(hR+1) := Nat.pow_le_pow_right (Nat.succ_pos q) (by omega)
  have yV : (q+1)^(hV+1) ≤ (q+1)^(hR+1) := Nat.pow_le_pow_right (Nat.succ_pos q) (by omega)
  have m2 := Nat.mul_le_mul_left (400 + 20*L) y2
  have mV := Nat.mul_le_mul_left (BlockPlatform.UnaryCalc.polyCoefficient hV cVc) yV
  have m1 := Nat.mul_le_mul_left 50 y1
  have e : (450 + 20*L + BlockPlatform.UnaryCalc.polyCoefficient hR C +
      BlockPlatform.UnaryCalc.polyCoefficient hV cVc) * (q+1)^(hR+1) =
      50*(q+1)^(hR+1) + (400 + 20*L)*(q+1)^(hR+1) +
      BlockPlatform.UnaryCalc.polyCoefficient hR C * (q+1)^(hR+1) +
      BlockPlatform.UnaryCalc.polyCoefficient hV cVc * (q+1)^(hR+1) := by ring
  dsimp only [prefixCost, res]
  rw [e]
  omega

/-- **Erasure condition.** Past an onset, every non-product tape of the pipeline (length
`≤ q + 3 + prefixCost`, `pipeline`) fits under the driver `Rc = C·tableClass L hR q`, for any
`C ≥ 1`, `hR ≥ 2` and `hV < hR`. The onset depends on `L C cVc hR hV`, all fixed before the input,
and the source may take its `base` above it. -/
theorem prefix_le_Rc (L C cVc : ℕ) (hC : 1 ≤ C) (h2 : 2 ≤ hR) (hVR : hV + 1 ≤ hR) :
    ∃ q0, ∀ q, q0 ≤ q → q + 3 + prefixCost hR hV L C cVc q ≤ C * RuntimeShape.tableClass L hR q := by
  set A := 450 + 20*L + BlockPlatform.UnaryCalc.polyCoefficient hR C +
    BlockPlatform.UnaryCalc.polyCoefficient hV cVc with hA
  obtain ⟨q1, h1⟩ := SupplierCapacity.coefficient_mul_logScale_pow_eventually_le (2*A + L + 1) 1
  refine ⟨max q1 600, fun q hq => ?_⟩
  have hs := prefixCost_split hR hV L C cVc q h2 hVR
  rw [← hA] at hs
  have hl := h1 q (le_of_max_le_left hq)
  rw [pow_one] at hl
  have hq600 : 600 ≤ q := le_of_max_le_right hq
  have hlg : 1 ≤ logScale q := by
    have := RuntimeShape.log_succ_le_logScale q
    omega
  -- 2A(q+1) ≤ 2^(q-K)
  have hY : q + 1 ≤ 2^(logScale q) := by
    have := RuntimeShape.succ_pow_le q 1
    simpa using this
  have hAA : 2*A < 2^(2*A) := Nat.lt_two_pow_self
  have hK : q - L*logScale q ≤ q - normalizedLiveCount q L := by
    unfold normalizedLiveCount
    omega
  have hsplit : (2*A + L + 1)*logScale q = 2*A*logScale q + L*logScale q + logScale q := by ring
  have hlin : 2*A ≤ 2*A*logScale q := Nat.le_mul_of_pos_right _ hlg
  have hexp : 2*A + logScale q ≤ q - normalizedLiveCount q L := by omega
  have hT : 2*A*(q+1) ≤ 2^(q - normalizedLiveCount q L) := by
    calc 2*A*(q+1) ≤ 2^(2*A) * 2^(logScale q) := Nat.mul_le_mul (le_of_lt hAA) hY
      _ = 2^(2*A + logScale q) := by rw [pow_add]
      _ ≤ 2^(q - normalizedLiveCount q L) := Nat.pow_le_pow_right (by decide) hexp
  -- 600(q+1) ≤ (q+1)^hR
  have hX : 600*(q+1) ≤ (q+1)^hR := by
    have h1' : (q+1)^2 ≤ (q+1)^hR := Nat.pow_le_pow_right (Nat.succ_pos q) h2
    have h2' : 600*(q+1) ≤ (q+1)*(q+1) := Nat.mul_le_mul_right _ (by omega)
    have e : (q+1)^2 = (q+1)*(q+1) := by ring
    omega
  -- combine
  set X := (q+1)^hR with hXdef
  set T := 2^(q - normalizedLiveCount q L) with hTdef
  have eA : (q+1)^(hR+1) = X*(q+1) := by rw [hXdef, pow_succ]
  have c1 : 2*(A*(X*(q+1))) ≤ X*T := by
    calc 2*(A*(X*(q+1))) = X*(2*A*(q+1)) := by ring
      _ ≤ X*T := Nat.mul_le_mul_left _ hT
  have c2 : 2*(300*((q+1)*T)) ≤ X*T := by
    calc 2*(300*((q+1)*T)) = (600*(q+1))*T := by ring
      _ ≤ X*T := Nat.mul_le_mul_right _ hX
  have c3 : X*T ≤ C*(X*T) := Nat.le_mul_of_pos_left _ hC
  have eT : RuntimeShape.tableClass L hR q = X*T := rfl
  rw [eT]
  rw [eA] at hs
  omega

/-- **Once, table class.** The whole pipeline costs `≤ c·tableClass L (hR+1) q` whenever
`hV < hR`, `2 ≤ hR`; the coefficient is explicit and `L`-free in its exponent. -/
theorem cost_class (L C cVc q : ℕ) (h2 : 2 ≤ hR) (hVR : hV + 1 ≤ hR) :
    cost hR hV L C cVc q ≤
      (450 + 20*L + BlockPlatform.UnaryCalc.polyCoefficient hR C +
        BlockPlatform.UnaryCalc.polyCoefficient hV cVc + 300 + 10*C + 6 + 10*cVc + 6 + 2) *
        RuntimeShape.tableClass L (hR+1) q := by
  have hs := prefixCost_split hR hV L C cVc q h2 hVR
  set T := RuntimeShape.tableClass L (hR+1) q with hTd
  have hT1 : 1 ≤ 2^(q - normalizedLiveCount q L) := Nat.one_le_two_pow
  have hpow : (q+1)^(hR+1) ≤ T := Nat.le_mul_of_pos_right _ hT1
  have htab : (q+1)*2^(q - normalizedLiveCount q L) ≤ T := by
    have : (q+1) ≤ (q+1)^(hR+1) := Nat.le_self_pow (by omega) _
    exact Nat.mul_le_mul_right _ this
  have hR' : (q+1)^hR*2^(q - normalizedLiveCount q L) ≤ T :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (Nat.succ_pos q) (by omega))
  have hV' : (q+1)^hV*2^(q - normalizedLiveCount q L) ≤ T :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (Nat.succ_pos q) (by omega))
  have hone : 1 ≤ T := SourceConstruction.one_le_tableClass L (hR+1) q
  have pH : 2*((C*(q+1)^hR)*(2*2^(q - normalizedLiveCount q L)+3)+2)+2 ≤ (10*C+6)*T := by
    have hd : C*(q+1)^hR*2^(q - normalizedLiveCount q L) ≤ C*T := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hR'
    have hd' : C*(q+1)^hR ≤ C*T := by
      calc C*(q+1)^hR ≤ C*((q+1)^hR*2^(q - normalizedLiveCount q L)) :=
            Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hT1)
        _ ≤ C*T := Nat.mul_le_mul_left _ hR'
    have e : 2*((C*(q+1)^hR)*(2*2^(q - normalizedLiveCount q L)+3)+2)+2 =
        4*(C*(q+1)^hR*2^(q - normalizedLiveCount q L)) + 6*(C*(q+1)^hR) + 6 := by ring
    have e2 : (10*C+6)*T = 10*(C*T) + 6*T := by ring
    rw [e, e2]
    omega
  have pJ : 2*((cVc*(q+1)^hV)*(2*2^(q - normalizedLiveCount q L)+3)+2)+2 ≤ (10*cVc+6)*T := by
    have hd : cVc*(q+1)^hV*2^(q - normalizedLiveCount q L) ≤ cVc*T := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hV'
    have hd' : cVc*(q+1)^hV ≤ cVc*T := by
      calc cVc*(q+1)^hV ≤ cVc*((q+1)^hV*2^(q - normalizedLiveCount q L)) :=
            Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hT1)
        _ ≤ cVc*T := Nat.mul_le_mul_left _ hV'
    have e : 2*((cVc*(q+1)^hV)*(2*2^(q - normalizedLiveCount q L)+3)+2)+2 =
        4*(cVc*(q+1)^hV*2^(q - normalizedLiveCount q L)) + 6*(cVc*(q+1)^hV) + 6 := by ring
    have e2 : (10*cVc+6)*T = 10*(cVc*T) + 6*T := by ring
    rw [e, e2]
    omega
  have m1 := Nat.mul_le_mul_left (450 + 20*L + BlockPlatform.UnaryCalc.polyCoefficient hR C +
      BlockPlatform.UnaryCalc.polyCoefficient hV cVc) hpow
  have m2 := Nat.mul_le_mul_left 300 htab
  have e : (450 + 20*L + BlockPlatform.UnaryCalc.polyCoefficient hR C +
      BlockPlatform.UnaryCalc.polyCoefficient hV cVc + 300 + 10*C + 6 + 10*cVc + 6 + 2) * T =
      (450 + 20*L + BlockPlatform.UnaryCalc.polyCoefficient hR C +
      BlockPlatform.UnaryCalc.polyCoefficient hV cVc) * T + 300*T + (10*C+6)*T + (10*cVc+6)*T + 2*T := by
    ring
  dsimp only [cost, res]
  rw [e]
  omega

end
end NearCubicWires.SourceConstruction.Dimension
end

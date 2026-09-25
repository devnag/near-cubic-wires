import Proof.Packets.BudgetCycleClass

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceBudget
open NearCubicWires NearCubicWires.Admission NearCubicWires.RuntimeShape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierEstimator

noncomputable section

/-! ## 1. Class tuples -/

/-- The six numbers of one `InClasses` statement (the divisor, live scale and the two scales are shared). -/
structure CostCls where
  dP : ℕ
  hT : ℕ
  hS : ℕ
  cP : ℕ
  cT : ℕ
  cS : ℕ

/-- `x` lies in the class `c`. -/
def CostCls.In (c : CostCls) (m L n qn x : ℕ) : Prop :=
  InClasses c.dP c.hT c.hS m L n qn c.cP c.cT c.cS x

/-- Pointwise domination of class tuples (exponents and coefficients). -/
def CostCls.Le (c d : CostCls) : Prop :=
  c.dP ≤ d.dP ∧ c.hT ≤ d.hT ∧ c.hS ≤ d.hS ∧ c.cP ≤ d.cP ∧ c.cT ≤ d.cT ∧ c.cS ≤ d.cS

theorem CostCls.In.mono_cls {c d : CostCls} {m L n qn x : ℕ} (h : c.Le d) (hx : c.In m L n qn x) :
    d.In m L n qn x := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact (InClasses.raise h1 h2 h3 hx).coeff_mono h4 h5 h6

/-- The join: maximal exponents, summed coefficients. -/
def CostCls.join (c d : CostCls) : CostCls :=
  ⟨max c.dP d.dP, max c.hT d.hT, max c.hS d.hS, c.cP + d.cP, c.cT + d.cT, c.cS + d.cS⟩

theorem CostCls.le_join_left (c d : CostCls) : c.Le (c.join d) :=
  ⟨le_max_left _ _, le_max_left _ _, le_max_left _ _, Nat.le_add_right _ _, Nat.le_add_right _ _,
    Nat.le_add_right _ _⟩

theorem CostCls.le_join_right (c d : CostCls) : d.Le (c.join d) :=
  ⟨le_max_right _ _, le_max_right _ _, le_max_right _ _, Nat.le_add_left _ _, Nat.le_add_left _ _,
    Nat.le_add_left _ _⟩

theorem CostCls.Le.trans {c d e : CostCls} (h1 : c.Le d) (h2 : d.Le e) : c.Le e := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h2
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5, a6.trans b6⟩

/-! ## 2. `V` and the workspace -/

/-- S's `V = cVc · tableClass L hV q` is in the table class alone. -/
theorem V_inClasses {dP hS m L n qn V cVc hV : ℕ} (hVc : V ≤ cVc * tableClass L hV qn) :
    InClasses dP hV hS m L n qn 0 cVc 0 V :=
  InClasses.table hVc

/-! ## 3. The family class and the per-call family fuel -/

/-- **The family class**: row count `N ≤ nC·(q+1)^nE`, widths `≤ xC·(n+1)^xE`, `V = cVc·tableClass L hV q`. -/
def famCls (printer : WilliamsAlgorithm) (cVc hV nC nE xC xE : ℕ) : CostCls :=
  ⟨nE + (nE + (xE + xE)), nE + hV, nE,
    (3*P1TopDownPaidPayload.tapes printer+6)*(nC*((2*P1TopDownPaidReusableReserves.coefficient printer+20)*1)) +
      (3*P1TopDownPaidPayload.tapes printer + 700)*((nC+1)*(xC+1)*(xC+1)),
    (3*P1TopDownPaidPayload.tapes printer+6)*(nC*((2*P1TopDownPaidReusableReserves.coefficient printer+20)*cVc)),
    0⟩

/-- **One call's family fuel in the family class** (`familyEntry_inClasses` at S's `V`). -/
theorem family_entry_in (printer : WilliamsAlgorithm) {m L n qn : ℕ} (V cVc hV : ℕ)
    (hVc : V ≤ cVc * tableClass L hV qn) (rowWidth b N D cnt nC nE xC xE : ℕ)
    (hNn : N ≤ nC*(n+1)^nE) (hNq : N ≤ nC*(qn+1)^nE)
    (hx : rowWidth + b + D + cnt + 1 ≤ xC*(n+1)^xE) :
    (famCls printer cVc hV nC nE xC xE).In m L n qn
      (familyEntryFuel printer (P1TopDownPaidReusableReserves.workspace printer V) rowWidth b N D cnt) := by
  have hV' : InClasses (nE + (xE + xE)) hV 0 m L n qn 0 cVc 0 V := V_inClasses hVc
  have hS := workspace_inClasses printer hV'
  have h := familyEntry_inClasses printer _ rowWidth b N D cnt nC nE xC xE hNn hNq hS hx le_rfl
  refine h.coeff_mono le_rfl le_rfl ?_
  simp

end
end NearCubicWires.SourceBudget


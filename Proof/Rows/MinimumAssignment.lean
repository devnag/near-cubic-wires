import Proof.Rows.Plan

/-! Evaluating the original gate on the physically readable minimizing assignment
is exactly its residual-constant flag; no threshold or weight rewrite is needed. -/
set_option autoImplicit false
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_MinimumAssignment
open NearCubicWires NearCubicWires.SupplierPipeline
open NearCubicWires.CompilerSemantics NearCubicWires.ThresholdCompiler
noncomputable section

def input {q : Nat} (g : NormalizedThresholdGate q) (live : Finset (Fin q))
    (x : BitInput q) : BitInput q := fun i => if i ∈ live then decide (g.weight i < 0) else x i

theorem live_eq {q : Nat} (g : NormalizedThresholdGate q) (live : Finset (Fin q)) (x : BitInput q) :
    liveScore g live (input g live x) = minimumLiveScore g live := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hn : g.weight i < 0 <;> simp [input,hi,hn,bitInt]

theorem frozen_eq {q : Nat} (g : NormalizedThresholdGate q) (live : Finset (Fin q)) (x : BitInput q) :
    frozenScore g live (input g live x) = frozenScore g live x := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  have hn := (Finset.mem_sdiff.mp hi).2
  simp [input,hn]

theorem eval_eq {q : Nat} (g : NormalizedThresholdGate q) (live : Finset (Fin q)) (x : BitInput q) :
    g.eval (input g live x) = residualConstant g live x := by
  classical
  unfold NormalizedThresholdGate.eval residualConstant
  apply decide_eq_decide.mpr
  have h := normalizedScore_split g live (input g live x)
  rw [live_eq,frozen_eq] at h
  change g.threshold ≤ (∑ i, g.weight i * bitInt (input g live x i)) ↔ _
  rw [h]
  omega
end
end PCJ45bee56da9f34d5a_MinimumAssignment

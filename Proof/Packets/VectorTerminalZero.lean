import Proof.Assembly.FixedCore

/-! The frozen terminal window is zero. Its normalized list is literally one
at coordinate zero and zero at every other coordinate, so no terminal atom
cache or window-provider execution is needed to initialize the vector. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorTerminal
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram

theorem shifted_zero (codes : List Nat) :
    Normalized.structuralGF2ShiftedElementarySymmetric codes 0 0=[[]] := by
  simp [Normalized.structuralGF2ShiftedElementarySymmetric,Normalized.structuralGF2Sum,
    Normalized.structuralGF2ElementarySymmetric,Normalized.structuralGF2Add,
    structuralGF2Zero,structuralGF2Scale,Ring.norm,Ring.add,Ring.canon,Ring.toggle]

theorem window_zero (codes : List Nat) (target : Nat) :
    Normalized.structuralGF2ConsecutiveWindowIndicator codes 0 0 target=
      if target=0 then [[]] else [] := by
  unfold Normalized.structuralGF2ConsecutiveWindowIndicator
  simp only [Nat.zero_add,List.range_one,List.map_cons,List.map_nil,shifted_zero]
  have hcoef : SupplierWindow.triangularCoefficient (SupplierWindow.windowDelta target) 0 =
      SupplierWindow.windowDelta target 0 := by
    rw [SupplierWindow.triangularCoefficient]
    simp
  rw [hcoef]
  by_cases ht:target=0
  · subst target
    simp [Normalized.structuralGF2Sum,Normalized.structuralGF2Add,structuralGF2Scale,
      SupplierWindow.windowDelta,structuralGF2Zero,Ring.add,Ring.toggle]
  · have ht' : 0 ≠ target := Ne.symm ht
    simp [Normalized.structuralGF2Sum,Normalized.structuralGF2Add,structuralGF2Scale,
      SupplierWindow.windowDelta,ht,ht',structuralGF2Zero,Ring.add,Ring.toggle]

theorem terminal_zero (depth population : Nat) (candidate : Fin (population+1)) :
    Normalized.structuralTerminalPolynomialVector depth population 0 candidate=
      if candidate.val=0 then [[]] else [] := by
  exact window_zero _ _

end PCJ9eff70d512234a4c_Fixed.Materializer.VectorTerminal

import Proof.Packets.PacketsXNormalizedRing

/-! Actual degree certificates through every normalized constructor. The degree
includes the graded-coordinate factor, as required by paper A.10 and A.13. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 120000
set_option linter.unusedVariables false
open NearCubicWires NearCubicWires.RepairSource
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierListPolynomial NearCubicWires.SupplierListSchedule
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierWalk NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierRadix
open CloseoutRawRows (structuralListCoordinateRawDegree structuralListCoordinateRawDegreeFrom)
namespace PCJ9eff70d512234a4c_Fixed.Normalized
noncomputable section

theorem degree_zero (degree : ℕ) :
    Ring.Degree degree structuralGF2Zero := by
  intro monomial hmonomial
  simp [structuralGF2Zero] at hmonomial

theorem degree_scale
    {degree : ℕ} (coefficient : ZMod 2)
    {polynomial : StructuralGF2Polynomial}
    (hdegree : Ring.Degree degree polynomial) :
    Ring.Degree degree
      (structuralGF2Scale coefficient polynomial) := by
  intro monomial hmonomial
  by_cases hzero : coefficient = 0
  · simp [structuralGF2Scale, hzero] at hmonomial
  · exact hdegree monomial (by
      simpa [structuralGF2Scale, hzero] using hmonomial)

theorem degree_sum
    {degree : Nat} {polynomials : List StructuralGF2Polynomial}
    (hpolynomials : ∀ P ∈ polynomials, Ring.Degree degree P) :
    Ring.Degree degree (structuralGF2Sum polynomials) := by
  unfold structuralGF2Sum
  have aux (A : StructuralGF2Polynomial) (hA : Ring.Degree degree A) :
      Ring.Degree degree (polynomials.foldl structuralGF2Add A) := by
    induction polynomials generalizing A with
    | nil => exact hA
    | cons P ps ih =>
      apply ih
      · intro Q hQ
        exact hpolynomials Q (by simp [hQ])
      · simpa only [structuralGF2Add, Nat.max_self] using Ring.degree_add hA (hpolynomials P (by simp))
  exact aux _ (degree_zero degree)

theorem degree_mul
    {leftDegree rightDegree : Nat} {left right : StructuralGF2Polynomial}
    (hleft : Ring.Degree leftDegree left) (hright : Ring.Degree rightDegree right) :
    Ring.Degree (leftDegree + rightDegree) (structuralGF2Mul left right) :=
  Ring.degree_mul hleft hright

theorem degree_elementarySymmetric
    (codes : List ℕ) (degree : ℕ) :
    Ring.Degree degree
      (structuralGF2ElementarySymmetric codes degree) := by
  apply Ring.degree_norm
  intro monomial hmonomial
  exact (List.mem_sublistsLen.mp hmonomial).2.le

theorem degree_shiftedElementarySymmetric
    (codes : List ℕ) (offset degree : ℕ) :
    Ring.Degree degree
      (structuralGF2ShiftedElementarySymmetric codes offset degree) := by
  unfold structuralGF2ShiftedElementarySymmetric
  apply degree_sum
  intro polynomial hpolynomial
  obtain ⟨indices, hindices, rfl⟩ := List.mem_map.mp hpolynomial
  apply degree_scale
  intro monomial hmonomial
  have hraw := degree_elementarySymmetric codes indices.1 monomial hmonomial
  have hsplit := List.Nat.mem_antidiagonal.mp hindices
  omega

theorem degree_consecutiveWindowIndicator
    (codes : List ℕ) (offset width target : ℕ) :
    Ring.Degree width
      (structuralGF2ConsecutiveWindowIndicator codes offset width target) := by
  unfold structuralGF2ConsecutiveWindowIndicator
  apply degree_sum
  intro polynomial hpolynomial
  obtain ⟨degree, hdegree, rfl⟩ := List.mem_map.mp hpolynomial
  apply degree_scale
  intro monomial hmonomial
  have hraw :=
    degree_shiftedElementarySymmetric codes offset degree monomial hmonomial
  have hdegreeLe := List.mem_range.mp hdegree
  omega

theorem degree_terminalPolynomialVector
    (depth population terminalWindow : ℕ)
    (candidate : Fin (population + 1)) :
    Ring.Degree terminalWindow
      (structuralTerminalPolynomialVector depth population terminalWindow
        candidate) := by
  unfold structuralTerminalPolynomialVector structuralTerminalWindowPolynomial
  exact degree_consecutiveWindowIndicator _ 0 terminalWindow candidate.val

theorem degree_deltaFactor
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (level : Fin depth)
    (parent child : Fin (population + 1)) :
    Ring.Degree (2 * window level)
      (structuralDeltaFactor label seed window level parent child) := by
  unfold structuralDeltaFactor
  dsimp only
  split
  · exact degree_zero _
  · unfold structuralDeltaWindowPolynomial
    dsimp only
    exact degree_consecutiveWindowIndicator _ _ _ _

theorem degree_combineListLevel
    {rank depth population childDegree : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (level : Fin depth)
    (childPolynomials : StructuralListPolynomialVector population)
    (hchildren : ∀ child,
      Ring.Degree childDegree (childPolynomials child))
    (parent : Fin (population + 1)) :
    Ring.Degree (childDegree + 2 * window level)
      (structuralCombineListLevel label seed window level childPolynomials
        parent) := by
  unfold structuralCombineListLevel
  apply degree_sum
  intro polynomial hpolynomial
  simp only [List.mem_ofFn] at hpolynomial
  obtain ⟨child, rfl⟩ := hpolynomial
  exact degree_mul (hchildren child)
    (degree_deltaFactor label seed window level parent child)

theorem degree_structuralListPolynomialVectorFrom
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow level : ℕ)
    (candidate : Fin (population + 1)) :
    Ring.Degree
      (structuralListCoordinateRawDegreeFrom depth window terminalWindow level)
      (structuralListPolynomialVectorFrom label seed window terminalWindow level
        candidate) := by
  rw [structuralListPolynomialVectorFrom,
    structuralListCoordinateRawDegreeFrom]
  by_cases hlevel : level < depth
  · rw [dif_pos hlevel, dif_pos hlevel]
    exact degree_combineListLevel label seed window ⟨level, hlevel⟩ _
      (fun child => degree_structuralListPolynomialVectorFrom label seed
        window terminalWindow (level + 1) child) candidate
  · rw [dif_neg hlevel, dif_neg hlevel]
    exact degree_terminalPolynomialVector depth population terminalWindow
      candidate
termination_by depth - level
decreasing_by omega

theorem degree_structuralListPolynomialVector
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (candidate : Fin (population + 1)) :
    Ring.Degree
      (structuralListCoordinateRawDegree depth window terminalWindow)
      (structuralListPolynomialVector label seed window terminalWindow
        candidate) := by
  unfold CloseoutRawRows.structuralListCoordinateRawDegree structuralListPolynomialVector
  exact degree_structuralListPolynomialVectorFrom label seed window
    terminalWindow 0 candidate

theorem degree_mono {a b : ℕ} {P : StructuralGF2Polynomial}
    (h : Ring.Degree a P) (hab : a ≤ b) : Ring.Degree b P :=
  fun m hm => (h m hm).trans hab

theorem degree_add {d : ℕ} {P Q : StructuralGF2Polynomial}
    (hP : Ring.Degree d P) (hQ : Ring.Degree d Q) :
    Ring.Degree d (structuralGF2Add P Q) := by
  simpa only [structuralGF2Add, Nat.max_self] using Ring.degree_add hP hQ

theorem degree_one (d : ℕ) : Ring.Degree d structuralGF2One := by
  intro m hm
  simp only [structuralGF2One,List.mem_singleton] at hm
  subst m
  simp





end
end PCJ9eff70d512234a4c_Fixed.Normalized

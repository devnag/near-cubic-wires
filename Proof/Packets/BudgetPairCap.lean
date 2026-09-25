import Proof.CaseAnalysis.RowsOriginalClause

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceBudget
open NearCubicWires NearCubicWires.RepairOrdinary
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound RepairRepresentation SourceInterfaces
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause

/-- `natBitLength n ≤ n + 1`. -/
theorem natBitLength_le_succ (n : ℕ) : natBitLength n ≤ n + 1 := by
  unfold natBitLength
  have := Nat.log_le_self 2 n
  omega

/-- One literal's parse cost, in its code `c = 2·index + negative`. -/
theorem literal_budget_le (i : ℕ) (s : Bool) :
    CloseoutRowsOriginalLiteral.budget i s ≤ 8*(2*i+s.toNat)*(2*i+s.toNat) + 34*(2*i+s.toNat) + 44 := by
  unfold CloseoutRowsOriginalLiteral.budget PCPPQueryNatural.budget MatrixDimensionPrepare.budget
  have hw := natBitLength_le_succ (2*i+s.toNat)
  have h1 : (2*i+s.toNat)*(8*natBitLength (2*i+s.toNat)+10) ≤ (2*i+s.toNat)*(8*((2*i+s.toNat)+1)+10) :=
    Nat.mul_le_mul_left _ (by omega)
  have e : (2*i+s.toNat)*(8*((2*i+s.toNat)+1)+10) = 8*(2*i+s.toNat)*(2*i+s.toNat) + 18*(2*i+s.toNat) := by ring
  omega

theorem pair_cap (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (i : Fin (2^(a.output r).clauseBits)) :
    CloseoutRowsOriginalPair.budget (index ((a.output r).clauses i).left)
        (index ((a.output r).clauses i).right) (negative ((a.output r).clauses i).left)
        (negative ((a.output r).clauses i).right) + 1 ≤
      PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity) := by
  obtain ⟨_, _, _, _, hsys, haux, _, _⟩ := PCPPQueryBounds.components a r
  set M := PCPPQueryBounds.scalar a (r.circuit.size + r.arity) with hM
  have hmaj := PCPPQueryCachedBounds.majorant_bound a (r.circuit.size + r.arity)
  have hlit : ∀ l : Literal ((a.output r).systematicBits + (a.output r).auxiliaryBits),
      2*index l + (negative l).toNat ≤ 4*M := by
    intro l
    have h := PCPPQueryBounds.literal_le l
    rw [literal_code] at h
    omega
  have hL := hlit ((a.output r).clauses i).left
  have hR := hlit ((a.output r).clauses i).right
  have bL := literal_budget_le (index ((a.output r).clauses i).left) (negative ((a.output r).clauses i).left)
  have bR := literal_budget_le (index ((a.output r).clauses i).right) (negative ((a.output r).clauses i).right)
  unfold CloseoutRowsOriginalPair.budget
  generalize 2*index ((a.output r).clauses i).left + (negative ((a.output r).clauses i).left).toNat = x at hL bL
  generalize 2*index ((a.output r).clauses i).right + (negative ((a.output r).clauses i).right).toNat = y at hR bR
  have hx2 : x*x ≤ (4*M)*(4*M) := Nat.mul_le_mul hL hL
  have hy2 : y*y ≤ (4*M)*(4*M) := Nat.mul_le_mul hR hR
  have e1 : 8*x*x = 8*(x*x) := by ring
  have e2 : 8*y*y = 8*(y*y) := by ring
  change _ ≤ _ at hmaj
  unfold PCPPQueryBounds.majorant at hmaj
  rw [← hM] at hmaj
  have hsq : (M+1)^2 = M*M + 2*M + 1 := by ring
  have e3 : (4*M)*(4*M) = 16*(M*M) := by ring
  rw [hsq] at hmaj
  rw [e3] at hx2 hy2
  omega

end NearCubicWires.SourceBudget


import Proof.SourceAssembly.SourceRequestSelLocalMach

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.SelLocal
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
open SourceInterfaces RepairSource.VerifierDecoding
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.SourceRequest.SelFront
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
noncomputable section

/-! ## Powers of the size bound -/

theorem pw_mono (M a b : Nat) (hM : 1 ≤ M) (h : a ≤ b) : M ^ a ≤ M ^ b := Nat.pow_le_pow_right hM h

theorem sq_ge (M : Nat) : M ≤ M ^ 2 := by
  rcases Nat.eq_zero_or_pos M with h | h
  · subst h; decide
  · calc M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ 2 := Nat.pow_le_pow_right h (by decide)

theorem mul_le_sq (x y M : Nat) (hx : x ≤ M) (hy : y ≤ M) : x * y ≤ M ^ 2 := by
  calc x * y ≤ M * M := Nat.mul_le_mul hx hy
    _ = M ^ 2 := (sq M).symm

theorem bitlen_le (n : Nat) : natBitLength n ≤ n + 1 := by
  unfold natBitLength
  have := Nat.log_le_self 2 n
  omega

theorem qnat_le (n M : Nat) (h : n ≤ M) (hM : 1 ≤ M) : PCPPQueryNatural.budget n ≤ 100 * M ^ 2 := by
  unfold PCPPQueryNatural.budget MatrixDimensionPrepare.budget
  have hw := bitlen_le n
  have h1 : n * (8 * natBitLength n + 10) ≤ M * (8 * (M + 1) + 10) :=
    Nat.mul_le_mul h (by omega)
  have h2 : M * (8 * (M + 1) + 10) = 8 * (M * M) + 18 * M := by ring
  have h3 : M * M = M ^ 2 := (sq M).symm
  have h4 := sq_ge M
  omega

theorem literal_le (i M : Nat) (s : Bool) (h : i ≤ M) (hM : 1 ≤ M) :
    CloseoutRowsOriginalLiteral.budget i s ≤ 1000 * M ^ 2 := by
  unfold CloseoutRowsOriginalLiteral.budget
  have hs : s.toNat ≤ 1 := Bool.toNat_le s
  have hq := qnat_le (2 * i + s.toNat) (3 * M) (by omega) (by omega)
  have e : (3 * M) ^ 2 = 9 * M ^ 2 := by ring
  have h4 := sq_ge M
  omega

theorem clean_le (i j C M : Nat) (s t : Bool) (hi : i ≤ M) (hj : j ≤ M) (hC : C ≤ M) (hM : 1 ≤ M) :
    CloseoutRowsOriginalPair.cleanBudget i j C s t ≤ 4100 * M ^ 2 := by
  unfold CloseoutRowsOriginalPair.cleanBudget CloseoutRowsOriginalPair.resetBudget CloseoutRowsOriginalPair.budget
  have h1 := literal_le i M s hi hM
  have h2 := literal_le j M t hj hM
  have h4 := sq_ge M
  omega

theorem nodeRead_le (a b c M : Nat) (ha : a ≤ M) (hb : b ≤ M) (hc : c ≤ M) (hM : 1 ≤ M) :
    PCPPNativeNodeRead.budget a b c ≤ 310 * M ^ 2 := by
  unfold PCPPNativeNodeRead.budget
  have h1 := qnat_le a M ha hM
  have h2 := qnat_le b M hb hM
  have h3 := qnat_le c M hc hM
  have h4 := sq_ge M
  omega

theorem metadata_le {n0 : Nat} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit) (M : Nat)
    (hs : p.systematicBits ≤ M) (ha : p.auxiliaryBits ≤ M) (hc : p.clauseBits ≤ M) (hr : r.arity ≤ M) (hM : 1 ≤ M) :
    CloseoutCaseTwo.Metadata.budget r p ≤ 700 * M ^ 2 := by
  unfold CloseoutCaseTwo.Metadata.budget CloseoutCaseTwo.Shape.budget CloseoutCaseTwo.Shape.rawBudget
    PCPPQueryField.fieldCost
  have h1 := nodeRead_le _ _ _ M hs ha hc hM
  have h3 : natBitLength 3 = 2 := by decide
  have h4 := sq_ge M
  omega

theorem prep_le (i s M : Nat) (hi : i ≤ M) : CloseoutCaseTwo.VariablePrep.budget i s ≤ 4 * M + 23 := by
  unfold CloseoutCaseTwo.VariablePrep.budget
  have := Nat.min_le_right s i
  omega

/-- **Front A's cost** (`SelFront.costA`): at most `5000 M²` once `M` dominates the cache capacity, the literal indices, the PCPP
shape counts and the arity. -/
theorem costA_le (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) (ci : Fin (2 ^ (a.output r).clauseBits))
    (M : Nat) (hM : 1 ≤ M)
    (hQ : PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity) ≤ M)
    (hL : index ((a.output r).clauses ci).left ≤ M) (hR : index ((a.output r).clauses ci).right ≤ M)
    (hs : (a.output r).systematicBits ≤ M) (ha : (a.output r).auxiliaryBits ≤ M) (hc : (a.output r).clauseBits ≤ M)
    (hr : r.arity ≤ M) :
    costA a r ci ≤ 5000 * M ^ 2 := by
  unfold costA LitInfo.litCost PCJ6e421fabe2aa4155_SourceLiteralRefs.sourceCost PCPPQueryCachedBounds.callBudget
  have h1 := clean_le _ _ _ M (negative ((a.output r).clauses ci).left) (negative ((a.output r).clauses ci).right) hL hR hQ hM
  have h2 := metadata_le r (a.output r) M hs ha hc hr hM
  have h3 := prep_le (index ((a.output r).clauses ci).left) (a.output r).systematicBits M hL
  have h4 := prep_le (index ((a.output r).clauses ci).right) (a.output r).systematicBits M hR
  have h5 := sq_ge M
  simp only at h1 ⊢
  omega

/-! ## Front B: the count readers, `word N`, the phase cursor -/

theorem sideCost_le (aux : Bool) (J M : Nat) (hJ : J ≤ M) :
    SourceFactorSel.Count.sideCost aux J ≤ 100 * (M + 1) ^ 4 := by
  have hJ1 : J ≤ M + 1 := by omega
  have p2 : J * J ≤ (M + 1) ^ 2 := mul_le_sq J J (M + 1) hJ1 hJ1
  have p3 : J * J * J ≤ (M + 1) ^ 3 := by
    calc J * J * J ≤ (M + 1) * (M + 1) * (M + 1) := Nat.mul_le_mul (Nat.mul_le_mul hJ1 hJ1) hJ1
      _ = (M + 1) ^ 3 := by ring
  have p4 : J * J * (J * J) ≤ (M + 1) ^ 4 := by
    calc J * J * (J * J) ≤ (M + 1) * (M + 1) * ((M + 1) * (M + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul hJ1 hJ1) (Nat.mul_le_mul hJ1 hJ1)
      _ = (M + 1) ^ 4 := by ring
  have o1 : 1 ≤ M + 1 := by omega
  have q12 : (M + 1) ^ 1 ≤ (M + 1) ^ 4 := pw_mono _ 1 4 o1 (by decide)
  have q22 : (M + 1) ^ 2 ≤ (M + 1) ^ 4 := pw_mono _ 2 4 o1 (by decide)
  have q32 : (M + 1) ^ 3 ≤ (M + 1) ^ 4 := pw_mono _ 3 4 o1 (by decide)
  have q1 : M + 1 = (M + 1) ^ 1 := (pow_one _).symm
  cases aux
  · simp only [SourceFactorSel.Count.sideCost, Bool.false_eq_true, if_false, SourceFactorSel.Count.sysCost]
    have e1 : J * (2 * J + 3) = 2 * (J * J) + 3 * J := by ring
    have e2 : J + J * J = J + J * J := rfl
    omega
  · simp only [SourceFactorSel.Count.sideCost, if_true, SourceFactorSel.Count.auxCost]
    have e1 : J * (2 * J + 3) = 2 * (J * J) + 3 * J := by ring
    have e2 : J * J * (2 * J + 3) = 2 * (J * J * J) + 3 * (J * J) := by ring
    have e3 : J * J * (2 * (J * J) + 3) = 2 * (J * J * (J * J)) + 3 * (J * J) := by ring
    omega

theorem countCostPh_le (ph : Phase) (sL sR nL nR : Bool) (JL JR M : Nat) (hL : JL ≤ M) (hR : JR ≤ M) :
    SourceFactorSel.Count.cost ph sL sR nL nR JL JR ≤ 1000 * (M + 1) ^ 4 := by
  have o1 : 1 ≤ M + 1 := by omega
  have q12 : (M + 1) ^ 1 ≤ (M + 1) ^ 4 := pw_mono _ 1 4 o1 (by decide)
  have q22 : (M + 1) ^ 2 ≤ (M + 1) ^ 4 := pw_mono _ 2 4 o1 (by decide)
  have q1 : M + 1 = (M + 1) ^ 1 := (pow_one _).symm
  cases ph with
  | penalty =>
    simp only [SourceFactorSel.Count.cost, SourceFactorSel.Count.penaltyCost]
    have s1 := sideCost_le (!sL) JL M hL
    have s2 := sideCost_le (!sR) JR M hR
    have l1 := SourceFactorSel.Count.penLen_le (!(!sL)) JL (M + 2) (by omega) (by omega)
    have l2 := SourceFactorSel.Count.penLen_le (!(!sR)) JR (M + 2) (by omega) (by omega)
    have m2 : (M + 2) * (M + 2) * ((M + 2) * (M + 2)) ≤ 16 * (M + 1) ^ 4 := by
      calc (M + 2) * (M + 2) * ((M + 2) * (M + 2)) ≤ (2 * (M + 1)) * (2 * (M + 1)) * ((2 * (M + 1)) * (2 * (M + 1))) :=
            Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (Nat.mul_le_mul (by omega) (by omega))
        _ = 16 * (M + 1) ^ 4 := by ring
    omega
  | moment =>
    simp only [SourceFactorSel.Count.cost, SourceFactorSel.Count.momentCost]
    have p2 : JL * JL ≤ (M + 1) ^ 2 := mul_le_sq JL JL (M + 1) (by omega) (by omega)
    have e1 : JL * (2 * JL + 3) = 2 * (JL * JL) + 3 * JL := by ring
    omega
  | clause =>
    simp only [SourceFactorSel.Count.cost, SourceFactorSel.Count.clauseCost]
    have ha : JL + nL.toNat ≤ M + 1 := by have := Bool.toNat_le nL; omega
    have hb : JR + nR.toNat ≤ M + 1 := by have := Bool.toNat_le nR; omega
    have p2 : (JL + nL.toNat) * (JR + nR.toNat) ≤ (M + 1) ^ 2 := mul_le_sq _ _ (M + 1) ha hb
    have e1 : (JL + nL.toNat) * (2 * (JR + nR.toNat) + 3) =
        2 * ((JL + nL.toNat) * (JR + nR.toNat)) + 3 * (JL + nL.toNat) := by ring
    omega

/-- **Front B's cost** (`SelFront.costB`): at most `2^26 (M+1)^4` once `M` dominates the witness length plus a literal index and the two
term counts. -/
theorem costB_le (ph : Phase) (bits : List Bool) (iL iR : Nat) (sL sR nL nR : Bool) (JL JR M : Nat)
    (hbL : bits.length + iL + 2 ≤ M) (hbR : bits.length + iR + 2 ≤ M) (hJL : JL ≤ M) (hJR : JR ≤ M) :
    costB ph bits iL iR sL sR nL nR JL JR ≤ 67108864 * (M + 1) ^ 4 := by
  unfold costB
  have c1 := SourceFactorSel.CountRead.countCost_le bits iL
  have c2 := SourceFactorSel.CountRead.countCost_le bits iR
  have o1 : 1 ≤ M + 1 := by omega
  have p3L : (bits.length + iL + 2) ^ 3 ≤ (M + 1) ^ 4 :=
    (Nat.pow_le_pow_left (by omega) 3).trans (pw_mono _ 3 4 o1 (by decide))
  have p3R : (bits.length + iR + 2) ^ 3 ≤ (M + 1) ^ 4 :=
    (Nat.pow_le_pow_left (by omega) 3).trans (pw_mono _ 3 4 o1 (by decide))
  have k := countCostPh_le ph sL sR nL nR JL JR M hJL hJR
  have cb : CurContract.curCost JL JR ≤ 4096 * (2 * (M + 1)) ^ 4 := by
    unfold CurContract.curCost CurContract.curBig
    have h : JL + JR + 2 ≤ 2 * (M + 1) := by omega
    have := Nat.pow_le_pow_left h 4
    have e : (JL + JR + 2) * (JL + JR + 2) * ((JL + JR + 2) * (JL + JR + 2)) = (JL + JR + 2) ^ 4 := by ring
    rw [e]; omega
  have e2 : (2 * (M + 1)) ^ 4 = 16 * (M + 1) ^ 4 := by ring
  have one : 1 ≤ (M + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  omega

end
end NearCubicWires.SourceRequest.SelLocal


import Proof.SourceAssembly.SourceRequestSelCostBack
import Proof.SourceAssembly.SourceRequestSelSymMach

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.SelLocal
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
open SourceInterfaces RepairSource.VerifierDecoding
open NearCubicWires.ComponentwiseBranchExtraction NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.SourceRequest.SelFront NearCubicWires.SourceRequest.SelBack
open NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec
open NearCubicWires.SourceRequest.CurContract (rhoOf)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
noncomputable section

/-- A cursor slot's term index is below the two term counts. -/
theorem fIdx_le (ph : Phase) (sL sR nL nR : Bool) (JL JR m i : Nat) :
    fIdx (facAt (selAt ph sL sR nL nR JL JR m) i) ≤ JL + JR := by
  unfold selAt
  cases h : (siteSel ph sL sR nL nR JL JR)[m]? with
  | none => simp [facAt, fIdx]
  | some s =>
    have hok := SourceFactorSel.SlotSpec.siteSel_ok ph sL sR nL nR JL JR s (List.mem_of_getElem? h)
    show fIdx (s.facs[i]?) ≤ JL + JR
    cases hf : s.facs[i]? with
    | none => simp [fIdx]
    | some f =>
      have hfok := hok f (List.mem_of_getElem? hf)
      cases f with
      | sys r => simp [fIdx]
      | term r j =>
        show j ≤ JL + JR
        cases r with
        | false =>
          have hj : j < JL := by simpa [SourceFactorSel.SlotSpec.FacOK] using hfok
          omega
        | true =>
          have hj : j < JR := by simpa [SourceFactorSel.SlotSpec.FacOK] using hfok
          omega

section
variable {n0 : Nat} {circuit : BooleanCircuit n0} {pcpp : PointwisePCPP circuit}

/-- The four slots' cost. -/
theorem fourCost_le (bits : List Bool) (iL iR : Nat) (σ : Option Sel) (cwid cw D W : Nat)
    (hbL : bits.length + iL + 2 ≤ W) (hbR : bits.length + iR + 2 ≤ W)
    (hidx : ∀ i, fIdx (facAt σ i) + 1 ≤ W) (hcwid : cwid ≤ W) (hcw : cw ≤ W) (hD : D ≤ W) :
    fourCostT bits iL iR σ cwid cw D ≤ 240000000000000000003 * W ^ 24 := by
  have hj : ∀ i, bits.length + (if fSide (facAt σ i) then iR else iL) + 2 ≤ W := by
    intro i; split <;> assumption
  have s0 := slotCost_le bits _ _ cwid cw D W (hj 0) (hidx 0) hcwid hcw hD
  have s1 := slotCost_le bits _ _ cwid cw D W (hj 1) (hidx 1) hcwid hcw hD
  have s2 := slotCost_le bits _ _ cwid cw D W (hj 2) (hidx 2) hcwid hcw hD
  have s3 := slotCost_le bits _ _ cwid cw D W (hj 3) (hidx 3) hcwid hcw hD
  have one : 1 ≤ W ^ 24 := Nat.one_le_pow _ _ (by omega)
  unfold fourCostT
  omega

/-- **The back's cost** (THR or SYM header mode; the four slots, the header block, the coefficient stage). -/
theorem backCost_le (mode : Bool) (T : Bool → List (CircuitMonomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom pcpp) 1))
    (bits : List Bool) (iL iR : Nat) (σ : Option Sel) (cwid cw D q L target k K b W : Nat) (hW4 : 4 ≤ W)
    (hbL : bits.length + iL + 2 ≤ W) (hbR : bits.length + iR + 2 ≤ W)
    (hidx : ∀ i, fIdx (facAt σ i) + 1 ≤ W) (hcwid : cwid ≤ W) (hcw : cw ≤ W) (hD : D ≤ W)
    (hq : q ≤ W) (hL : L ≤ W) (ht : target ≤ W) (hk : k ≤ W) (hK : K ≤ W) (hb : b ≤ W) (hcw1 : 1 ≤ cw)
    (hT : ∀ r, ∀ mo ∈ T r, mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw)
    (hTV : ∀ r, ∀ mo ∈ T r, mo.coefficient.num.natAbs < W ∧ mo.coefficient.den < W)
    (hrb : (rhoOf σ).num.natAbs < 2 ^ CurContract.rhoW ∧ (rhoOf σ).den < 2 ^ CurContract.rhoW) :
    fourCostT bits iL iR σ cwid cw D + 1 + (SourceFactorSel.HdrBlock.hdrCost mode q L target k D + 1 +
      SourceFactorSel.CoefR.coefRCost cw CurContract.rhoW K b (rhoOf σ) (fun i => fTerm (facAt σ i.val))
        (fun i => SourceFactorSel.CoefBridge.tco T (facAt σ i.val))) ≤ 250000000000000000000 * (W + 1) ^ 24 := by
  have f := fourCost_le bits iL iR σ cwid cw D W hbL hbR hidx hcwid hcw hD
  have h := hdrCost_le mode q L target k D W hq hL ht hk hD
  have c := coefRCost_le cw K b W (rhoOf σ) (fun i => fTerm (facAt σ i.val))
    (fun i => SourceFactorSel.CoefBridge.tco T (facAt σ i.val)) hW4 hcw hK hb hrb
    (fun i _ => tco_V T W (by omega) hTV (facAt σ i.val)) (fun i _ => tco_bits T cw hcw1 hT (facAt σ i.val))
  have w1 : W ^ 24 ≤ (W + 1) ^ 24 := Nat.pow_le_pow_left (by omega) 24
  have w2 : W ^ 10 ≤ (W + 1) ^ 24 :=
    (Nat.pow_le_pow_left (by omega) 10).trans (Nat.pow_le_pow_right (by omega) (by decide))
  have w3 : (W + 1) ^ 2 ≤ (W + 1) ^ 24 := Nat.pow_le_pow_right (by omega) (by decide)
  have one : 1 ≤ (W + 1) ^ 24 := Nat.one_le_pow _ _ (by omega)
  omega

end

theorem selThrCost_le (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) (ci : Fin (2 ^ (a.output r).clauseBits))
    (coordinate : Fin ((a.output r).systematicBits + (a.output r).auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom (a.output r)) 1)
    (bits : List Bool) (ph : Phase) (L target cwid cw D b m W : Nat) (hW4 : 4 ≤ W)
    (hQ : PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity) ≤ W)
    (hs : (a.output r).systematicBits ≤ W) (ha : (a.output r).auxiliaryBits ≤ W) (hc : (a.output r).clauseBits ≤ W)
    (hr : r.arity ≤ W)
    (hbL : bits.length + (literalIndex ((a.output r).clauses ci).left).val + 2 ≤ W)
    (hbR : bits.length + (literalIndex ((a.output r).clauses ci).right).val + 2 ≤ W)
    (hJ : (coordinate (literalIndex ((a.output r).clauses ci).left)).monomials.length +
      (coordinate (literalIndex ((a.output r).clauses ci).right)).monomials.length + 1 ≤ W)
    (hcwid : cwid ≤ W) (hcw : cw ≤ W) (hD : D ≤ W) (hL : L ≤ W) (ht : target ≤ W)
    (hK : 2 ^ (a.output r).clauseBits ≤ W) (hb : b ≤ W) (hcw1 : 1 ≤ cw)
    (hcoef : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw)
    (hcoefV : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < W ∧ mo.coefficient.den < W) :
    selThrCost a r ci coordinate bits ph L target cwid cw D b m ≤ 300000000000000000000 * (W + 1) ^ 24 := by
  have hA := costA_le a r ci W (by omega) hQ (by show (literalIndex ((a.output r).clauses ci).left).val ≤ W; omega)
    (by show (literalIndex ((a.output r).clauses ci).right).val ≤ W; omega) hs ha hc hr
  have hB := costB_le ph bits (literalIndex ((a.output r).clauses ci).left).val
    (literalIndex ((a.output r).clauses ci).right).val
    (decide ((literalIndex ((a.output r).clauses ci).left).val < (a.output r).systematicBits))
    (decide ((literalIndex ((a.output r).clauses ci).right).val < (a.output r).systematicBits))
    (literalNegated ((a.output r).clauses ci).left) (literalNegated ((a.output r).clauses ci).right)
    (coordinate (literalIndex ((a.output r).clauses ci).left)).monomials.length
    (coordinate (literalIndex ((a.output r).clauses ci).right)).monomials.length W hbL hbR (by omega) (by omega)
  have hT : ∀ rr, ∀ mo ∈ Tof coordinate ci rr, mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw := by
    intro rr mo hmo; cases rr <;> exact hcoef _ mo hmo
  have hTV : ∀ rr, ∀ mo ∈ Tof coordinate ci rr, mo.coefficient.num.natAbs < W ∧ mo.coefficient.den < W := by
    intro rr mo hmo; cases rr <;> exact hcoefV _ mo hmo
  have hidx : ∀ i, fIdx (facAt (sigmaOf a r ci coordinate ph m) i) + 1 ≤ W := fun i => by
    have := fIdx_le ph (decide ((literalIndex ((a.output r).clauses ci).left).val < (a.output r).systematicBits))
      (decide ((literalIndex ((a.output r).clauses ci).right).val < (a.output r).systematicBits))
      (literalNegated ((a.output r).clauses ci).left) (literalNegated ((a.output r).clauses ci).right)
      (coordinate (literalIndex ((a.output r).clauses ci).left)).monomials.length
      (coordinate (literalIndex ((a.output r).clauses ci).right)).monomials.length m i
    unfold sigmaOf; omega
  have hk : (FactorLoop.factorsAt coordinate ph ci m).length ≤ W := (FactorLoop.factorsAt_le coordinate ph ci m).trans (by omega)
  have hbk := backCost_le false (Tof coordinate ci) bits (literalIndex ((a.output r).clauses ci).left).val
    (literalIndex ((a.output r).clauses ci).right).val (sigmaOf a r ci coordinate ph m) cwid cw D r.arity L target
    (FactorLoop.factorsAt coordinate ph ci m).length (2 ^ (a.output r).clauseBits) b W hW4 hbL hbR hidx hcwid hcw hD hr hL ht
    hk hK hb hcw1 hT hTV (SelRho.rho_bits _ _ _ _ _ _ _ _)
  have w1 : W ^ 2 ≤ (W + 1) ^ 24 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by decide))
  have w2 : (W + 1) ^ 4 ≤ (W + 1) ^ 24 := Nat.pow_le_pow_right (by omega) (by decide)
  unfold selThrCost backThrCost
  omega

theorem selSymCost_le (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) (ci : Fin (2 ^ (a.output r).clauseBits))
    (coordinate : Fin ((a.output r).systematicBits + (a.output r).auxiliaryBits) →
      CircuitPolynomial (RepairSource.CloseoutFinal.C10TotalDecode.Atom (a.output r)) 1)
    (bits : List Bool) (ph : Phase) (L target cwid cw D b m W : Nat) (hW4 : 4 ≤ W)
    (hQ : PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity) ≤ W)
    (hs : (a.output r).systematicBits ≤ W) (ha : (a.output r).auxiliaryBits ≤ W) (hc : (a.output r).clauseBits ≤ W)
    (hr : r.arity ≤ W)
    (hbL : bits.length + (literalIndex ((a.output r).clauses ci).left).val + 2 ≤ W)
    (hbR : bits.length + (literalIndex ((a.output r).clauses ci).right).val + 2 ≤ W)
    (hJ : (coordinate (literalIndex ((a.output r).clauses ci).left)).monomials.length +
      (coordinate (literalIndex ((a.output r).clauses ci).right)).monomials.length + 1 ≤ W)
    (hcwid : cwid ≤ W) (hcw : cw ≤ W) (hD : D ≤ W) (hL : L ≤ W) (ht : target ≤ W)
    (hK : 2 ^ (a.output r).clauseBits ≤ W) (hb : b ≤ W) (hcw1 : 1 ≤ cw)
    (hcoef : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw)
    (hcoefV : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < W ∧ mo.coefficient.den < W) :
    selSymCost a r ci coordinate bits ph L target cwid cw D b m ≤ 300000000000000000000 * (W + 1) ^ 24 := by
  have hA := costA_le a r ci W (by omega) hQ (by show (literalIndex ((a.output r).clauses ci).left).val ≤ W; omega)
    (by show (literalIndex ((a.output r).clauses ci).right).val ≤ W; omega) hs ha hc hr
  have hB := costB_le ph bits (literalIndex ((a.output r).clauses ci).left).val
    (literalIndex ((a.output r).clauses ci).right).val
    (decide ((literalIndex ((a.output r).clauses ci).left).val < (a.output r).systematicBits))
    (decide ((literalIndex ((a.output r).clauses ci).right).val < (a.output r).systematicBits))
    (literalNegated ((a.output r).clauses ci).left) (literalNegated ((a.output r).clauses ci).right)
    (coordinate (literalIndex ((a.output r).clauses ci).left)).monomials.length
    (coordinate (literalIndex ((a.output r).clauses ci).right)).monomials.length W hbL hbR (by omega) (by omega)
  have hT : ∀ rr, ∀ mo ∈ Tof coordinate ci rr, mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw := by
    intro rr mo hmo; cases rr <;> exact hcoef _ mo hmo
  have hTV : ∀ rr, ∀ mo ∈ Tof coordinate ci rr, mo.coefficient.num.natAbs < W ∧ mo.coefficient.den < W := by
    intro rr mo hmo; cases rr <;> exact hcoefV _ mo hmo
  have hidx : ∀ i, fIdx (facAt (sigmaOf a r ci coordinate ph m) i) + 1 ≤ W := fun i => by
    have := fIdx_le ph (decide ((literalIndex ((a.output r).clauses ci).left).val < (a.output r).systematicBits))
      (decide ((literalIndex ((a.output r).clauses ci).right).val < (a.output r).systematicBits))
      (literalNegated ((a.output r).clauses ci).left) (literalNegated ((a.output r).clauses ci).right)
      (coordinate (literalIndex ((a.output r).clauses ci).left)).monomials.length
      (coordinate (literalIndex ((a.output r).clauses ci).right)).monomials.length m i
    unfold sigmaOf; omega
  have hk : (FactorLoop.factorsAt coordinate ph ci m).length ≤ W := (FactorLoop.factorsAt_le coordinate ph ci m).trans (by omega)
  have hbk := backCost_le true (Tof coordinate ci) bits (literalIndex ((a.output r).clauses ci).left).val
    (literalIndex ((a.output r).clauses ci).right).val (sigmaOf a r ci coordinate ph m) cwid cw D r.arity L target
    (FactorLoop.factorsAt coordinate ph ci m).length (2 ^ (a.output r).clauseBits) b W hW4 hbL hbR hidx hcwid hcw hD hr hL ht
    hk hK hb hcw1 hT hTV (SelRho.rho_bits _ _ _ _ _ _ _ _)
  have w1 : W ^ 2 ≤ (W + 1) ^ 24 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by decide))
  have w2 : (W + 1) ^ 4 ≤ (W + 1) ^ 24 := Nat.pow_le_pow_right (by omega) (by decide)
  have e4 : SelBackSym.fourCostS = fourCostT := rfl
  unfold selSymCost SelBackSym.backSymCost
  rw [e4]
  omega

end
end NearCubicWires.SourceRequest.SelLocal


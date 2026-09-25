import Proof.Packets.BudgetPairCap
import Proof.SourceAssembly.SourceFactorSelWordsWin
import Proof.SourceAssembly.SourceRequestSelCostTotal
import Proof.SourceAssembly.SourceRequestSelG7Spec

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest
open NearCubicWires.SourceFactorSel.Words NearCubicWires.SourceFactorSel.WordsHost
open NearCubicWires.SourceRequest.SelLocal (resW resWS)
open NearCubicWires.SourceRequest.CurContract (curBig rhoW)
open NearCubicWires.SourceRequest.TermReader (rawTerms)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
open NearCubicWires.SourceRequest.SelLocal (resW resWS)
open NearCubicWires.SourceRequest.CurContract (curBig rhoW)
open NearCubicWires.SourceRequest.TermReader (rawTerms)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
open NearCubicWires.SourceRequest.SelLocal (resW resWS)
open NearCubicWires.SourceRequest.CurContract (curBig rhoW)
open NearCubicWires.SourceRequest.TermReader (rawTerms)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
open NearCubicWires.SourceRequest.SelLocal (resW resWS)
open NearCubicWires.SourceRequest.CurContract (curBig rhoW)
open NearCubicWires.SourceRequest.TermReader (rawTerms)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
namespace NearCubicWires.SourceRequest.SelWinCore
open NearCubicWires.SourceFactorSel NearCubicWires.SourceFactorSel.AtS
open NearCubicWires.SourceRequest.SelG7Spec (g7costW)
noncomputable section
attribute [local irreducible] NearCubicWires.P1TopDownPaidPayload.tapes

/-! ## 1. Arithmetic -/

theorem add_pow_le (x y d : Nat) : (x + y) ^ d ≤ 2 ^ d * (x ^ d + y ^ d) := by
  rcases le_total x y with h | h
  · have h1 : (x + y) ^ d ≤ (2 * y) ^ d := Nat.pow_le_pow_left (by omega) d
    have h2 : (2 * y) ^ d = 2 ^ d * y ^ d := mul_pow 2 y d
    have h3 : 2 ^ d * y ^ d ≤ 2 ^ d * (x ^ d + y ^ d) := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
    omega
  · have h1 : (x + y) ^ d ≤ (2 * x) ^ d := Nat.pow_le_pow_left (by omega) d
    have h2 : (2 * x) ^ d = 2 ^ d * x ^ d := mul_pow 2 x d
    have h3 : 2 ^ d * x ^ d ≤ 2 ^ d * (x ^ d + y ^ d) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    omega

theorem pow_le_pow25 (x d : Nat) (hd : d ≤ 25) : (x + 1) ^ d ≤ (x + 1) ^ 25 := Nat.pow_le_pow_right (by omega) hd

/-! ## 2. The call's shape counts are below the cache capacity -/

theorem shapes_le (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) :
    r.arity ≤ PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity) ∧
    (a.output r).systematicBits ≤ PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity) ∧
    (a.output r).auxiliaryBits ≤ PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity) ∧
    2 ^ (a.output r).clauseBits ≤ PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity) ∧
    (a.output r).clauseBits ≤ PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity) := by
  obtain ⟨_, _, har, _, hsys, haux, h2c, hcl⟩ := PCPPQueryBounds.components a r
  have hmaj := PCPPQueryCachedBounds.majorant_bound a (r.circuit.size + r.arity)
  have hM : PCPPQueryBounds.scalar a (r.circuit.size + r.arity) ≤ PCPPQueryBounds.majorant a (r.circuit.size + r.arity) := by
    unfold PCPPQueryBounds.majorant
    nlinarith
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-! ## 3. The window bundle -/

/-- **`g7Spec`'s `Rc` windows**, in its exact types (the header block's field cap `c` is a parameter). -/
structure G7Win (sources : EightSources) (mask : MaskProducer) (MB : List Bool) (a : PointwisePCPPAlgorithm)
    (rq : PCPPRequest a.minimumArity)
    (coordinate : Fin ((a.output rq).systematicBits + (a.output rq).auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom (a.output rq)) 1)
    (bits : List Bool) (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ (a.output rq).clauseBits))
    (L target : Nat) (mode : Bool) (Rc b cwid cw D c Vb Pw W Ld : Nat) : Prop where
  hc : CloseoutRowsOriginalPair.budget (index ((a.output rq).clauses ci).left)
      (index ((a.output rq).clauses ci).right) (negative ((a.output rq).clauses ci).left)
      (negative ((a.output rq).clauses ci).right) + 1 ≤ PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity)
  hwinA : litCost a rq ci (PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity)) + 1 ≤ Rc
  hQR : PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity) + 1 ≤ Rc
  hiL : index ((a.output rq).clauses ci).left + 3 ≤ Rc
  hiR : index ((a.output rq).clauses ci).right + 3 ≤ Rc
  hcL : SourceFactorSel.CountRead.countCost bits (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).left).val + 1 ≤ Rc
  hcR : SourceFactorSel.CountRead.countCost bits (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).right).val + 1 ≤ Rc
  hbig : curBig (coordinate (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).left)).monomials.length
      (coordinate (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).right)).monomials.length ≤ Rc
  hwinR : ∀ (jj idx : Nat) (ts : List (ℚ × Nat)), (jj = (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).left).val ∨
      jj = (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).right).val) → rawTerms bits jj = some ts → idx < ts.length →
      TermCompose.readerCost bits jj idx cwid cw + 1 ≤ Rc
  hHfit : ∀ m, m ≤ (FactorLoop.monomials coordinate ph ci).length →
      SourceFactorSel.HdrBlock.Fits mode rq.arity L target (FactorLoop.factorsAt coordinate ph ci m).length c D Rc Rc Rc Rc
  hbigR : SourceFactorSel.CoefR.coefBigR Vb (2 ^ (a.output rq).clauseBits) b (cw + rhoW) ≤ Rc
  hNw : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * (requestAt coordinate ph ci L target mode m).nativeWord.length + 1 ≤ Rc
  hS : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci L target mode m).supportWord (decompositionOf sources)).length + 1 ≤ Rc
  hT : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci L target mode m).topWord (decompositionOf sources)).length + 1 ≤ Rc
  cq : ∀ m, m ≤ (monomials coordinate ph ci).length → 4 * (requestAt coordinate ph ci L target mode m).q + 3 ≤ Rc
  ck : ∀ m, m ≤ (monomials coordinate ph ci).length →
      4 * normalizedLiveCount (requestAt coordinate ph ci L target mode m).q
        (requestAt coordinate ph ci L target mode m).liveScale + 3 ≤ Rc
  cm : ∀ m, m ≤ (monomials coordinate ph ci).length →
      4 * ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources)).occurrences.length + 3 ≤ Rc
  ci' : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci L target mode m).indexWord (decompositionOf sources)).length + 1 ≤ Rc
  hneed : ∀ m, m ≤ (monomials coordinate ph ci).length → ((NearCubicWires.SourceStart.Bank.sb (decompositionOf sources))).need (requestAt coordinate ph ci L target mode m) ≤ Rc
  cl1 : ∀ m, m ≤ (monomials coordinate ph ci).length →
      2 * ((requestAt coordinate ph ci L target mode m).input (decompositionOf sources)).length + 1 ≤ Rc
  cl2 : 2 * MB.length + 1 ≤ Rc
  hwin : ∀ m, m ≤ (monomials coordinate ph ci).length →
      g7costW sources mask MB a rq ci coordinate bits ph L target cwid cw D b Pw W Ld mode m + 1 ≤ Rc
  hDR : D ≤ Rc
  hDC : D + 1 ≤ Rc
  hRc1 : 1 ≤ Rc

/-! ## 4. The per-mode pieces of `g7costW` -/

def selW (a : PointwisePCPPAlgorithm) (rq : PCPPRequest a.minimumArity) (ci : Fin (2 ^ (a.output rq).clauseBits))
    (coordinate : Fin ((a.output rq).systematicBits + (a.output rq).auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom (a.output rq)) 1)
    (bits : List Bool) (ph : CloseoutRowsOriginalSchedule.Phase) (L target cwid cw D b : Nat) : Bool → Nat → Nat
  | false, m => SelLocal.selThrCost a rq ci coordinate bits ph L target cwid cw D b m
  | true, m => SelLocal.selSymCost a rq ci coordinate bits ph L target cwid cw D b m

def loopW (sources : EightSources) (a : PointwisePCPPAlgorithm) (rq : PCPPRequest a.minimumArity)
    (ci : Fin (2 ^ (a.output rq).clauseBits))
    (coordinate : Fin ((a.output rq).systematicBits + (a.output rq).auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom (a.output rq)) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (L target Pw W Ld : Nat) : Bool → Nat → Nat
  | false, m => FactorLoop.cost (SelBack.PT (pcpp := a.output rq) (decompositionOf sources) Pw W Ld) L target
      (FactorLoop.factorsAt coordinate ph ci m)
  | true, m => FactorLoop.cost (SelBackSym.PS (pcpp := a.output rq) (decompositionOf sources) Pw W Ld) L target
      (FactorLoop.factorsAt coordinate ph ci m)

theorem g7costW_eq (sources : EightSources) (mask : MaskProducer) (MB : List Bool) (a : PointwisePCPPAlgorithm)
    (rq : PCPPRequest a.minimumArity) (ci : Fin (2 ^ (a.output rq).clauseBits))
    (coordinate : Fin ((a.output rq).systematicBits + (a.output rq).auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom (a.output rq)) 1)
    (bits : List Bool) (ph : CloseoutRowsOriginalSchedule.Phase) (L target cwid cw D b Pw W Ld : Nat) (mode : Bool) (m : Nat) :
    g7costW sources mask MB a rq ci coordinate bits ph L target cwid cw D b Pw W Ld mode m =
      selW a rq ci coordinate bits ph L target cwid cw D b mode m + 1 +
        (loopW sources a rq ci coordinate ph L target Pw W Ld mode m + 1 +
          Words.wordsCost mask (NearCubicWires.SourceStart.Bank.sb (decompositionOf sources))
            (requestAt coordinate ph ci L target mode m) MB) := by
  cases mode <;> rfl

/-! ## 5. The two table parts -/

/-- The `n`-part plus the `q`-part. -/
def Ebd (n Sq cL dL wC wE : Nat) : Nat := 2 ^ 200 * (n + 1) ^ 25 + cL * (n + 1) ^ dL + 2 ^ 200 * (Sq + 1) ^ 25 + wC * (Sq + 1) ^ wE

theorem Ebd_le (n Sq cL dL wC wE T : Nat) (hN : 2 * (2 ^ 200 * (n + 1) ^ 25 + cL * (n + 1) ^ dL) ≤ T)
    (hS : 2 * (2 ^ 200 * (Sq + 1) ^ 25 + wC * (Sq + 1) ^ wE) ≤ T) : Ebd n Sq cL dL wC wE ≤ T := by
  unfold Ebd; omega

theorem q_le_E (n Sq cL dL wC wE x : Nat) (h : x ≤ 2 ^ 200 * (Sq + 1) ^ 25) : x ≤ Ebd n Sq cL dL wC wE := by
  unfold Ebd; omega

theorem mix_le_E (n Sq cL dL wC wE x : Nat) (h : x ≤ 2 ^ 200 * ((n + 1) ^ 25 + (Sq + 1) ^ 25)) :
    x ≤ Ebd n Sq cL dL wC wE := by
  unfold Ebd
  have e : 2 ^ 200 * ((n + 1) ^ 25 + (Sq + 1) ^ 25) = 2 ^ 200 * (n + 1) ^ 25 + 2 ^ 200 * (Sq + 1) ^ 25 := by ring
  omega

/-- A small polynomial of `Sq` (degree `≤ 25`, coefficient `≤ 2^100`) is in the `q`-part. -/
theorem small_q (Sq c d x : Nat) (hc : c ≤ 2 ^ 100) (hd : d ≤ 25) (h : x ≤ c * (Sq + 1) ^ d) :
    x ≤ 2 ^ 200 * (Sq + 1) ^ 25 := by
  have h1 : (Sq + 1) ^ d ≤ (Sq + 1) ^ 25 := pow_le_pow25 Sq d hd
  have h2 : c * (Sq + 1) ^ d ≤ 2 ^ 100 * (Sq + 1) ^ 25 := Nat.mul_le_mul hc h1
  have h3 : 2 ^ 100 * (Sq + 1) ^ 25 ≤ 2 ^ 200 * (Sq + 1) ^ 25 :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by decide))
  omega

/-- A mixed power `(n + 1 + k·(Sq+1))^d`, `d ≤ 25`, `k ≤ 7`, with coefficient `≤ 2^100`, is in the two parts. -/
theorem mixed (n Sq k c d x : Nat) (hk : k ≤ 7) (hc : c ≤ 2 ^ 100) (hd : d ≤ 25) (h : x ≤ c * (n + 1 + k * (Sq + 1)) ^ d) :
    x ≤ 2 ^ 200 * ((n + 1) ^ 25 + (Sq + 1) ^ 25) := by
  have h1 := add_pow_le (n + 1) (k * (Sq + 1)) d
  have h2 : (n + 1) ^ d ≤ (n + 1) ^ 25 := pow_le_pow25 n d hd
  have h3a : k ^ d ≤ 8 ^ 25 := (Nat.pow_le_pow_left (by omega) d).trans (Nat.pow_le_pow_right (by decide) hd)
  have h3 : (k * (Sq + 1)) ^ d ≤ 8 ^ 25 * (Sq + 1) ^ 25 := by
    rw [mul_pow]; exact Nat.mul_le_mul h3a (pow_le_pow25 Sq d hd)
  have h4 : 2 ^ d ≤ 2 ^ 25 := Nat.pow_le_pow_right (by decide) hd
  have h5 : (n + 1 + k * (Sq + 1)) ^ d ≤ 2 ^ 25 * ((n + 1) ^ 25 + 8 ^ 25 * (Sq + 1) ^ 25) :=
    h1.trans (Nat.mul_le_mul h4 (by omega))
  have h6 : c * (n + 1 + k * (Sq + 1)) ^ d ≤ 2 ^ 100 * (2 ^ 25 * ((n + 1) ^ 25 + 8 ^ 25 * (Sq + 1) ^ 25)) :=
    Nat.mul_le_mul hc h5
  have e : 2 ^ 100 * (2 ^ 25 * ((n + 1) ^ 25 + 8 ^ 25 * (Sq + 1) ^ 25)) =
      2 ^ 125 * (n + 1) ^ 25 + 2 ^ 200 * (Sq + 1) ^ 25 := by ring
  have e2 : 2 ^ 200 * ((n + 1) ^ 25 + (Sq + 1) ^ 25) = 2 ^ 200 * (n + 1) ^ 25 + 2 ^ 200 * (Sq + 1) ^ 25 := by ring
  have h7 : 2 ^ 125 * (n + 1) ^ 25 ≤ 2 ^ 200 * (n + 1) ^ 25 :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by decide))
  omega

/-! ## 6. The windows, one at a time -/

section win
variable (a : PointwisePCPPAlgorithm) (rq : PCPPRequest a.minimumArity) (ci : Fin (2 ^ (a.output rq).clauseBits))
  (n Sq cL dL wC wE Rc : Nat) (hE : Ebd n Sq cL dL wC wE ≤ Rc)

include hE in
theorem w_q (x c d : Nat) (hc : c ≤ 2 ^ 100) (hd : d ≤ 25) (h : x ≤ c * (Sq + 1) ^ d) : x ≤ Rc :=
  (q_le_E n Sq cL dL wC wE x (small_q Sq c d x hc hd h)).trans hE

include hE in
theorem w_mix (x k c d : Nat) (hk : k ≤ 7) (hc : c ≤ 2 ^ 100) (hd : d ≤ 25) (h : x ≤ c * (n + 1 + k * (Sq + 1)) ^ d) :
    x ≤ Rc :=
  (mix_le_E n Sq cL dL wC wE x (mixed n Sq k c d x hk hc hd h)).trans hE

theorem idx_lt (hQ : PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity) ≤ Sq)
    (l : Literal ((a.output rq).systematicBits + (a.output rq).auxiliaryBits)) :
    (NearCubicWires.ComponentwiseBranchExtraction.literalIndex l).val + 1 ≤ 2 * Sq := by
  obtain ⟨_, hsys, haux, _, _⟩ := shapes_le a rq
  have := (NearCubicWires.ComponentwiseBranchExtraction.literalIndex l).isLt
  omega

include hE in
theorem w_QR (hQ : PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity) ≤ Sq) :
    PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity) + 1 ≤ Rc :=
  w_q n Sq cL dL wC wE Rc hE _ 1 1 (by decide) (by decide) (by rw [pow_one]; omega)

include hE in
theorem w_idx (hQ : PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity) ≤ Sq)
    (l : Literal ((a.output rq).systematicBits + (a.output rq).auxiliaryBits)) : index l + 3 ≤ Rc := by
  have h := idx_lt a rq Sq hQ l
  have e : index l = (NearCubicWires.ComponentwiseBranchExtraction.literalIndex l).val := rfl
  exact w_q n Sq cL dL wC wE Rc hE _ 3 1 (by decide) (by decide) (by rw [pow_one]; omega)

include hE in
theorem w_litCost (hQ : PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity) ≤ Sq) (h4 : 4 ≤ Sq) :
    litCost a rq ci (PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity)) + 1 ≤ Rc := by
  obtain ⟨har, hsys, haux, _, hcl⟩ := shapes_le a rq
  have hl := idx_lt a rq Sq hQ ((a.output rq).clauses ci).left
  have hr := idx_lt a rq Sq hQ ((a.output rq).clauses ci).right
  have hA := SelLocal.costA_le a rq ci (2 * Sq) (by omega) (by omega)
    (by show (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).left).val ≤ 2 * Sq; omega)
    (by show (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).right).val ≤ 2 * Sq; omega)
    (by omega) (by omega) (by omega) (by omega)
  have hle : litCost a rq ci (PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity)) + 1 ≤ SelFront.costA a rq ci := by
    unfold SelFront.costA; omega
  have hsq : (2 * Sq) ^ 2 ≤ 4 * (Sq + 1) ^ 2 := by
    rw [mul_pow]; exact Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left (by omega) 2)
  exact w_q n Sq cL dL wC wE Rc hE _ 20000 2 (by norm_num) (by decide) (by omega)

include hE in
theorem w_count (bits : List Bool) (hbits : bits.length ≤ n)
    (hQ : PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity) ≤ Sq)
    (l : Literal ((a.output rq).systematicBits + (a.output rq).auxiliaryBits)) :
    SourceFactorSel.CountRead.countCost bits (NearCubicWires.ComponentwiseBranchExtraction.literalIndex l).val + 1 ≤ Rc := by
  have h := SourceFactorSel.CountRead.countCost_le bits (NearCubicWires.ComponentwiseBranchExtraction.literalIndex l).val
  have hl := idx_lt a rq Sq hQ l
  have hb : bits.length + (NearCubicWires.ComponentwiseBranchExtraction.literalIndex l).val + 2 ≤ n + 1 + 2 * (Sq + 1) := by omega
  have hp : (bits.length + (NearCubicWires.ComponentwiseBranchExtraction.literalIndex l).val + 2) ^ 3 ≤
      (n + 1 + 2 * (Sq + 1)) ^ 3 := Nat.pow_le_pow_left hb 3
  have h1 : 1 ≤ (n + 1 + 2 * (Sq + 1)) ^ 3 := Nat.one_le_pow _ _ (by omega)
  exact w_mix n Sq cL dL wC wE Rc hE _ 2 16777217 3 (by decide) (by norm_num) (by decide) (by omega)

include hE in
theorem w_big (JL JR : Nat) (hJ : JL + JR + 1 ≤ Sq) : curBig JL JR ≤ Rc := by
  unfold curBig
  have h1 : JL + JR + 2 ≤ Sq + 1 := by omega
  have h2 : (JL + JR + 2) * (JL + JR + 2) * ((JL + JR + 2) * (JL + JR + 2)) ≤ (Sq + 1) ^ 4 := by
    have := Nat.mul_le_mul h1 h1
    have := Nat.mul_le_mul this this
    have e : (Sq + 1) ^ 4 = (Sq + 1) * (Sq + 1) * ((Sq + 1) * (Sq + 1)) := by ring
    omega
  exact w_q n Sq cL dL wC wE Rc hE _ 64 4 (by norm_num) (by decide) (by omega)

include hE in
theorem w_reader (bits : List Bool) (jj idx cwid cw : Nat) (hbits : bits.length ≤ n) (hjj : jj + 1 ≤ 2 * Sq)
    (hidx : idx + 1 ≤ Sq) (hcwid : cwid ≤ Sq) (hcw : cw ≤ Sq) :
    TermCompose.readerCost bits jj idx cwid cw + 1 ≤ Rc := by
  have h := SelLocal.readerCost_le bits jj idx cwid cw (bits.length + 3 * Sq + 3) (by omega) (by omega) (by omega) (by omega)
  have hb : bits.length + 3 * Sq + 3 ≤ n + 1 + 3 * (Sq + 1) := by omega
  have hp : (bits.length + 3 * Sq + 3) ^ 24 ≤ (n + 1 + 3 * (Sq + 1)) ^ 24 := Nat.pow_le_pow_left hb 24
  have h1 : 1 ≤ (n + 1 + 3 * (Sq + 1)) ^ 24 := Nat.one_le_pow _ _ (by omega)
  exact w_mix n Sq cL dL wC wE Rc hE _ 3 50000000000000000001 24 (by decide) (by norm_num) (by decide) (by omega)

include hE in
theorem w_D (D : Nat) (hD : D ≤ Sq) : D + 1 ≤ Rc :=
  w_q n Sq cL dL wC wE Rc hE _ 1 1 (by decide) (by decide) (by rw [pow_one]; omega)

include hE in
theorem w_one : 1 ≤ Rc := by
  have := hE; unfold Ebd at this
  have h : 1 ≤ 2 ^ 200 * (n + 1) ^ 25 := Nat.mul_pos (by positivity) (Nat.one_le_pow _ _ (by omega))
  omega

include hE in
theorem w_coefBig (Vb K b cw : Nat) (hV : Vb ≤ Sq) (hK : K ≤ Sq) (hb : b ≤ Sq) (hcw : cw ≤ Sq) :
    SourceFactorSel.CoefR.coefBigR Vb K b (cw + rhoW) ≤ Rc := by
  unfold SourceFactorSel.CoefR.coefBigR rhoW
  have h5 : Vb ^ 5 ≤ (Sq + 1) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  have h6 : Vb ^ 5 * (K + 1) ≤ (Sq + 1) ^ 5 * (Sq + 1) := Nat.mul_le_mul h5 (by omega)
  have e : (Sq + 1) ^ 5 * (Sq + 1) = (Sq + 1) ^ 6 := by ring
  have h1 : Sq + 1 ≤ (Sq + 1) ^ 6 := by
    have := Nat.pow_le_pow_right (show 0 < Sq + 1 by omega) (show 1 ≤ 6 by decide); rw [pow_one] at this; exact this
  exact w_q n Sq cL dL wC wE Rc hE _ 300 6 (by norm_num) (by decide) (by nlinarith)

include hE in
theorem w_words (r : Request) (MB : List Bool) (A : DecompositionAlgorithm) (hY : WordsCost.Yb A (r, MB) ≤ Sq) :
    8 * WordsCost.Yb A (r, MB) ≤ Rc :=
  w_q n Sq cL dL wC wE Rc hE _ 8 1 (by decide) (by decide) (by rw [pow_one]; omega)

include hE in
theorem w_need (r : Request) (MB : List Bool) (A : DecompositionAlgorithm) (hY : WordsCost.Yb A (r, MB) ≤ Sq) :
    (NearCubicWires.SourceStart.Bank.sb A).need r ≤ Rc := by
  have h := WordsCost.need_sb_le A r MB
  have h2 : (2 * WordsCost.Yb A (r, MB)) ^ 3 ≤ 8 * (Sq + 1) ^ 3 := by
    rw [mul_pow]; exact Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left (by omega) 3)
  exact w_q n Sq cL dL wC wE Rc hE _ 134217728 3 (by norm_num) (by decide) (by omega)

end win

/-! ## 7. The header block, the cost, and the core -/

theorem field_le_header (mode : Bool) (q L target k : Nat) (i : Fin 5) :
    (SourceFactorSel.Header.fields mode q L target k i).length ≤ (SourceRequest.header mode q L target k).length := by
  rw [← SourceFactorSel.Header.fields_flatten, List.length_flatten]
  apply List.le_sum_of_mem
  exact List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩

section win2
variable (n Sq cL dL wC wE Rc : Nat) (hE : Ebd n Sq cL dL wC wE ≤ Rc)

include hE in
theorem w_fits (mode : Bool) (q L target k D : Nat) (hq : q ≤ Sq) (hL : L ≤ Sq) (ht : target ≤ Sq) (hk : k ≤ 4)
    (h4 : 4 ≤ Sq) (h4D : 4 ≤ D) (hD : D ≤ Sq) :
    SourceFactorSel.HdrBlock.Fits mode q L target k (20 * Sq + 50) D Rc Rc Rc Rc := by
  have hh := SelLocal.header_len mode q L target k Sq hq hL ht (by omega)
  have hcR : 20 * Sq + 50 ≤ Rc := w_q n Sq cL dL wC wE Rc hE _ 50 1 (by norm_num) (by decide) (by rw [pow_one]; omega)
  have hDR := w_D n Sq cL dL wC wE Rc hE D hD
  refine ⟨?_, by omega, by omega, hDR, ?_, hcR, hcR, ?_⟩
  · unfold CloseoutRowsEstimatorParity.Capacity.value
    have : (k + 1) ^ 2 ≤ 25 := by
      have := Nat.pow_le_pow_left (show k + 1 ≤ 5 by omega) 2; norm_num at this ⊢; omega
    exact w_q n Sq cL dL wC wE Rc hE _ 6400 0 (by norm_num) (by decide) (by rw [pow_zero]; omega)
  · intro i
    have := field_le_header mode q L target k i
    omega
  · exact w_q n Sq cL dL wC wE Rc hE _ 41 1 (by norm_num) (by decide) (by rw [pow_one]; omega)

end win2

/-- **The selection cost of either mode** under the size facts (the `W` of `selThrCost_le`/`selSymCost_le` is `|bits| + 4·Sq + 4`). -/
theorem selW_le (a : PointwisePCPPAlgorithm) (rq : PCPPRequest a.minimumArity) (ci : Fin (2 ^ (a.output rq).clauseBits))
    (coordinate : Fin ((a.output rq).systematicBits + (a.output rq).auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom (a.output rq)) 1)
    (bits : List Bool) (ph : CloseoutRowsOriginalSchedule.Phase) (L target cwid cw D b Vb Sq : Nat) (mode : Bool) (m : Nat)
    (hQ : PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity) ≤ Sq)
    (hJ : (coordinate (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).left)).monomials.length +
      (coordinate (NearCubicWires.ComponentwiseBranchExtraction.literalIndex ((a.output rq).clauses ci).right)).monomials.length + 1 ≤ Sq)
    (hcwidS : cwid ≤ Sq) (hcwS : cw ≤ Sq) (hDS : D ≤ Sq) (hLS : L ≤ Sq) (htS : target ≤ Sq) (hbS : b ≤ Sq) (hVbS : Vb ≤ Sq)
    (hcw1 : 1 ≤ cw)
    (hcoef : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw)
    (hcoefV : ∀ j, ∀ mo ∈ (coordinate j).monomials, mo.coefficient.num.natAbs < Vb ∧ mo.coefficient.den < Vb) :
    selW a rq ci coordinate bits ph L target cwid cw D b mode m ≤
      300000000000000000000 * (bits.length + 4 * Sq + 4 + 1) ^ 24 := by
  obtain ⟨har, hsys, haux, h2c, hcl⟩ := shapes_le a rq
  have hl := idx_lt a rq Sq hQ ((a.output rq).clauses ci).left
  have hr := idx_lt a rq Sq hQ ((a.output rq).clauses ci).right
  have hV : ∀ j, ∀ mo ∈ (coordinate j).monomials,
      mo.coefficient.num.natAbs < bits.length + 4 * Sq + 4 ∧ mo.coefficient.den < bits.length + 4 * Sq + 4 := by
    intro j mo hmo
    have := hcoefV j mo hmo
    omega
  cases mode with
  | false =>
    exact SelLocal.selThrCost_le a rq ci coordinate bits ph L target cwid cw D b m (bits.length + 4 * Sq + 4) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) hcw1 hcoef hV
  | true =>
    exact SelLocal.selSymCost_le a rq ci coordinate bits ph L target cwid cw D b m (bits.length + 4 * Sq + 4) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) hcw1 hcoef hV

end
end NearCubicWires.SourceRequest.SelWinCore
end

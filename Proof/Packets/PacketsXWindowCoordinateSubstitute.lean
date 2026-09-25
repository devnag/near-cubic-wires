import Proof.Packets.PacketsXLiteralVectorSubstitution
import Proof.Packets.PacketsXWindowLevelAtoms
import Proof.Packets.PacketsXWindowSubstitutionDock

/-! One actual whole-coordinate substitution after the complete literal
vector has been built. Private backing is reset physically on every call. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierListPolynomial NearCubicWires.RepairSource.CloseoutRawRows
open NormalizedFiniteTransport SubstitutionCensus Theorem25Completion.CycleBounds

attribute [local irreducible] Workspace.machine substitute
noncomputable def coordinateSubstitute := Composition.machine Workspace.machine substitute
def coordinateSubstituteBudget (C R count : Nat) := (2*R+4)+1+SubstitutionCall.totalBudget C R count

theorem coordinate_substitute_run {rank depth population : Nat}
    (C w d : Nat) (hC : (depth+2*population+2)^2≤C) (hw : 1≤w)
    (mask : Finset (Fin population)) (label : Fin population→BinaryVector rank) (seed : ToeplitzSeed rank)
    (wins : Fin depth→Nat) (candidate : Fin (population+1))
    (hd : structuralListCoordinateRawDegree depth wins 0≤d)
    (hfit : (population+1)^d≤2^w) (hfitAtom : population+1≤2^w)
    (hliteral : (population*(2*depth+1)+2)^d≤2^w)
    (atoms : List (Ring.Poly Nat)) (hlen : atoms.length=C)
    (hatoms : ∀Q∈atoms,Bounded (Finset.range population) 1 Q)
    (hmeaning : ∀level : Fin depth,∀slot : Fin (2*population),
      atoms.getD (Nat.pair (level.val+1) slot.val) []=
        Normalized.structuralListLiteralAtom (depth:=depth) mask label seed (Nat.pair (level.val+1) slot.val))
    (left : Ring.Poly Nat) (hl : left.length≤2^w) (A : Fin 256→List Bool)
    (hengine : ∀i : Fin 34,A (i.castAdd 222)=ReusableArithmetic.state C (commonReserve C w)
      (left.map (maskNat C))
      ((Normalized.structuralListPolynomialVector label seed wins 0 candidate).map (maskNat C)) i)
    (abank : A 140=PacketVector.bank (commonReserve C w) (SubstitutionOuter.atomMasks C atoms))
    (hwork : ∀i,Workspace.selected i→(A i).length≤commonReserve C w) :
    let P:=Normalized.structuralListPolynomialVector label seed wins 0 candidate
    Step coordinateSubstitute (coordinateSubstituteBudget C (commonReserve C w) P.length) heads A heads
      (operands (commonReserve C w) ((SubstitutionCall.leftResult atoms P left).map (maskNat C))
        ((Normalized.structuralMaskedListCoordinate mask label seed wins 0 candidate).map (maskNat C))
        (Workspace.cleared (commonReserve C w) A)) := by
  dsimp only
  let P:=Normalized.structuralListPolynomialVector label seed wins 0 candidate
  have good:=LiteralAlphabet.good_vectorFrom label seed wins 0 0 candidate
  have hP : SubstitutionInvariant.Good C P := by
    refine ⟨?_,good.1⟩
    intro m hm code hc
    exact (LiteralAlphabet.codes_lt_square depth population code (good.2 m hm code hc)).trans_le hC
  have degree : Ring.Degree d P:=Normalized.degree_mono
    (Normalized.degree_structuralListPolynomialVector label seed wins 0 candidate) hd
  have count : P.length≤2^w:=
    (LiteralAlphabet.size_le good degree).trans hliteral
  have popC : population<C := by
    have hbase : population+1≤depth+2*population+2:=by omega
    have hpow : depth+2*population+2≤(depth+2*population+2)^2:=Nat.le_self_pow (by decide) _
    omega
  have hS : ∀j∈Finset.range population,j<C:=fun j hj=>(Finset.mem_range.mp hj).trans popC
  have first:=Workspace.run (commonReserve C w) heads A workspace_heads (hengine 32) (hengine 33) hwork
  have input:=Workspace.substitution_ready C (commonReserve C w) (left.map (maskNat C))
    (P.map (maskNat C)) A hengine
  rw [abank] at input
  have last:=substitute_run C w d (Finset.range population) hS hw
    (by simpa only [Finset.card_range] using hfit) (by simpa only [Finset.card_range] using hfitAtom)
    P hP degree count atoms hlen hatoms left hl heads (Workspace.cleared (commonReserve C w) A)
    (by decide) input
  rw [LiteralVectorSubstitution.coordinate mask label seed wins candidate atoms hmeaning] at last
  simpa only [coordinateSubstitute,coordinateSubstituteBudget,P] using first.seq last

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider

import Proof.Packets.PacketsXVectorWorkerProviderDock
import Proof.Packets.PacketsXWindowCoordinateBoundary

/-! Focus the closed whole-coordinate substitution into the actual vector
controller. It acts after final-coordinate lookup and retains all banks,
indices, saved fold accumulator, and the numeric controller workspace. -/
set_option autoImplicit false
set_option maxHeartbeats 950000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierListPolynomial NearCubicWires.RepairSource.CloseoutRawRows
open NormalizedFiniteTransport SubstitutionCensus Theorem25Completion.CycleBounds
noncomputable section

def coordinateCallback:=RecoveryFocus.machine providerSlots WindowProvider.coordinateSubstitute

theorem provider_heads_eq : providerH=WindowProvider.heads := by
  funext i
  refine Fin.addCases (m:=34) (n:=222) (fun j=>?_) (fun j=>?_) i
  · simp only [providerH,Fin.addCases_left,ReusableArithmetic.heads,WindowProvider.heads,Fin.ext_iff,Fin.val_castAdd]
    rfl
  · have hn:j.natAdd 34≠(31 : Fin 256) := by
      intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega
    simp only [providerH,Fin.addCases_right,WindowProvider.heads,if_neg hn]

attribute [local irreducible] WindowProvider.coordinateSubstitute coordinateCallback

theorem coordinate_callback_run {rank depth population : Nat}
    (C w d pi li : Nat) (hC : (depth+2*population+2)^2≤C) (hw : 1≤w)
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
    (left : Ring.Poly Nat) (hl : left.length≤2^w) (acc : List (List Bool)) (previous next : List Bool)
    (fields : Fin 222→List Bool) (extra : Fin 32→List Bool)
    (abank : fields 106=PacketVector.bank (commonReserve C w) (SubstitutionOuter.atomMasks C atoms))
    (hwork : ∀i,WindowProvider.Workspace.selected i→
      (providerA C (commonReserve C w) (left.map (maskNat C))
        ((Normalized.structuralListPolynomialVector label seed wins 0 candidate).map (maskNat C)) fields i).length≤commonReserve C w) :
    let R:=commonReserve C w
    let P:=Normalized.structuralListPolynomialVector label seed wins 0 candidate
    let outLeft:=(SubstitutionCall.leftResult atoms P left).map (maskNat C)
    let outRight:=(Normalized.structuralMaskedListCoordinate mask label seed wins 0 candidate).map (maskNat C)
    let T:=WindowProvider.operands R outLeft outRight
      (WindowProvider.Workspace.cleared R (providerA C R (left.map (maskNat C)) (P.map (maskNat C)) fields))
    Step coordinateCallback (WindowProvider.coordinateSubstituteBudget C R P.length) (H (fun _=>0))
      (A C R candidate.val pi li (left.map (maskNat C)) (P.map (maskNat C)) acc previous next fields extra)
      (H (fun _=>0))
      (A C R candidate.val pi li outLeft outRight acc previous next (fun j=>T (j.natAdd 34)) extra) := by
  dsimp only
  let R:=commonReserve C w
  let P:=Normalized.structuralListPolynomialVector label seed wins 0 candidate
  let S:=providerA C R (left.map (maskNat C)) (P.map (maskNat C)) fields
  have core : ∀i : Fin 34,S (i.castAdd 222)=ReusableArithmetic.state C R (left.map (maskNat C)) (P.map (maskNat C)) i :=
    fun i=>Fin.addCases_left i
  have h:=WindowProvider.coordinate_substitute_run C w d hC hw mask label seed wins candidate hd hfit hfitAtom
    hliteral atoms hlen hatoms hmeaning left hl S core abank hwork
  dsimp only at h
  rw [←provider_heads_eq] at h
  unfold coordinateCallback
  apply provider_dock C R candidate.val pi li _ _ _ _ acc previous next fields extra _ h
  apply WindowProvider.operands_core C R (left.map (maskNat C)) (P.map (maskNat C))
  intro i
  exact (WindowProvider.Workspace.core_retained R S i).trans (core i)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp

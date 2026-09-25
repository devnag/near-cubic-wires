import Proof.Packets.PacketsXVectorLiteralDensePolys
import Proof.Packets.PacketsXVectorCoordinateCallback

/-! Whole-coordinate substitution from the actual completed literal bank.
All atom support, capacity and semantic obligations are discharged by the
concrete descending bank producer. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.RepairSource.CloseoutRawRows
open CloseoutRowsModeCache NormalizedFiniteTransport Theorem25Completion.CycleBounds SubstitutionCensus
noncomputable section

def completedAtoms (C population active depth : Nat) (mask : Finset (Fin population))
    (seed : ToeplitzSeed (canonicalGradedRank population active)) : List (Ring.Poly Nat) :=
  densePolys population depth (parameters population active 0 (C+9) mask seed) (List.replicate C []) depth

theorem completed_atoms_length (C population active depth : Nat) (mask : Finset (Fin population))
    (seed : ToeplitzSeed (canonicalGradedRank population active)) :
    (completedAtoms C population active depth mask seed).length=C := by
  rw [completedAtoms,dense_polys_length,List.length_replicate]

theorem completed_atoms_bounded (C population active depth : Nat) (mask : Finset (Fin population))
    (seed : ToeplitzSeed (canonicalGradedRank population active)) :
    ∀P∈completedAtoms C population active depth mask seed,Bounded (Finset.range population) 1 P := by
  apply dense_polys_bounded
  intro P hP
  have he : P=[] := (List.mem_replicate.mp hP).2
  subst P
  exact NormalizedIntermediate.zero _ _

theorem completed_atoms_meaning (C population active depth : Nat) (mask : Finset (Fin population))
    (seed : ToeplitzSeed (canonicalGradedRank population active))
    (hd : depth≤canonicalGradedRank population active) (hC : (depth+2*population+2)^2≤C)
    (level : Fin depth) (slot : Fin (2*population)) :
    (completedAtoms C population active depth mask seed).getD (Nat.pair (level.val+1) slot.val) []=
      Normalized.structuralListLiteralAtom (depth:=depth) mask (canonicalGradedLabel population active) seed
        (Nat.pair (level.val+1) slot.val) :=
  dense_polys_delta_meaning C population active depth depth mask seed _ (List.length_replicate ..)
    hd hC le_rfl level (by omega) slot.val slot.isLt

theorem completed_atoms_masks (C population active depth : Nat) (mask : Finset (Fin population))
    (seed : ToeplitzSeed (canonicalGradedRank population active)) (hC : population≤C) :
    denseLevels C population depth (parameters population active 0 (C+9) mask seed) (List.replicate C []) depth=
      SubstitutionOuter.atomMasks C (completedAtoms C population active depth mask seed) := by
  simpa only [List.map_replicate,List.map_nil,SubstitutionOuter.atomMasks,completedAtoms] using
    dense_polys_masks C population depth (parameters population active 0 (C+9) mask seed) (List.replicate C []) hC depth

theorem literal_coordinate_run (C w d population active depth pi li : Nat)
    (mask : Finset (Fin population)) (seed : ToeplitzSeed (canonicalGradedRank population active))
    (wins : Fin depth → Nat) (candidate : Fin (population+1))
    (hd : depth≤canonicalGradedRank population active) (hC : (depth+2*population+2)^2≤C) (hw : 1≤w)
    (hdegree : structuralListCoordinateRawDegree depth wins 0≤d)
    (hfit : (population+1)^d≤2^w) (hfitAtom : population+1≤2^w)
    (hliteral : (population*(2*depth+1)+2)^d≤2^w)
    (left : Ring.Poly Nat) (hl : left.length≤2^w) (acc : PacketVector.Packet) (previous next : List Bool)
    (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool)
    (abank : fields 106=PacketVector.bank (commonReserve C w)
      (denseLevels C population depth (parameters population active 0 (C+9) mask seed) (List.replicate C []) depth))
    (hready : ProviderReady C (commonReserve C w) fields) :
    let R:=commonReserve C w
    let P:=Normalized.structuralListPolynomialVector (canonicalGradedLabel population active) seed wins 0 candidate
    let outLeft:=(SubstitutionCall.leftResult (completedAtoms C population active depth mask seed) P left).map (maskNat C)
    let outRight:=(Normalized.structuralMaskedListCoordinate mask (canonicalGradedLabel population active) seed wins 0 candidate).map (maskNat C)
    let T:=WindowProvider.operands R outLeft outRight
      (WindowProvider.Workspace.cleared R (providerA C R (left.map (maskNat C)) (P.map (maskNat C)) fields))
    Step coordinateCallback (WindowProvider.coordinateSubstituteBudget C R P.length) (H (fun _=>0))
      (A C R candidate.val pi li (left.map (maskNat C)) (P.map (maskNat C)) acc previous next fields extra)
      (H (fun _=>0))
      (A C R candidate.val pi li outLeft outRight acc previous next (fun j=>T (j.natAdd 34)) extra) := by
  have hpopulation : population≤C := by
    have bound : depth+2*population+2≤(depth+2*population+2)^2:=Nat.le_self_pow (by decide) _
    omega
  rw [completed_atoms_masks C population active depth mask seed hpopulation] at abank
  exact coordinate_callback_run C w d pi li hC hw mask (canonicalGradedLabel population active) seed wins candidate
    hdegree hfit hfitAtom hliteral (completedAtoms C population active depth mask seed)
    (completed_atoms_length C population active depth mask seed)
    (completed_atoms_bounded C population active depth mask seed)
    (completed_atoms_meaning C population active depth mask seed hd hC) left hl acc previous next fields extra abank
    (hready.work _ _)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp

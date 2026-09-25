import Proof.Packets.PacketsXVectorLiteralCoordinateGuards
import Proof.Packets.PacketsXVectorCoordinateZeroLeft
import Proof.Packets.PacketsXVectorCoordinateReentry

/-! A fixed whole-coordinate callback accepting any fitting previous left
operand. Reset, exact substitution, output capacities, and reentry are all
closed concrete execution/layout theorems. -/
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

def literalCoordinateCallback:=Composition.machine clearCoordinateLeft coordinateCallback
def literalCoordinateFuel (C w : Nat):=4*commonReserve C w+6+4398046511104*(C+1)^9*2^(17*w)

theorem literal_coordinate_reset_run (C w d population active depth pi li : Nat)
    (mask : Finset (Fin population)) (seed : ToeplitzSeed (canonicalGradedRank population active))
    (wins : Fin depth → Nat) (candidate : Fin (population+1))
    (hd : depth≤canonicalGradedRank population active) (hC : (depth+2*population+2)^2≤C) (hw : 1≤w)
    (hdegree : structuralListCoordinateRawDegree depth wins 0≤d)
    (hfit : (population+1)^d≤2^w) (hfitAtom : population+1≤2^w)
    (hliteral : (population*(2*depth+1)+2)^d≤2^w)
    (left acc : PacketVector.Packet) (previous next : List Bool)
    (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool)
    (hl : VectorAccumulator.Fits (commonReserve C w) left)
    (abank : fields 106=PacketVector.bank (commonReserve C w)
      (denseLevels C population depth (parameters population active 0 (C+9) mask seed) (List.replicate C []) depth))
    (hready : ProviderReady C (commonReserve C w) fields) :
    let R:=commonReserve C w
    let P:=Normalized.structuralListPolynomialVector (canonicalGradedLabel population active) seed wins 0 candidate
    let outLeft:=(SubstitutionCall.leftResult (completedAtoms C population active depth mask seed) P []).map (maskNat C)
    let outRight:=(Normalized.structuralMaskedListCoordinate mask (canonicalGradedLabel population active) seed wins 0 candidate).map (maskNat C)
    let f:=coordinateFields C R [] (P.map (maskNat C)) outLeft outRight fields
    Step literalCoordinateCallback (literalCoordinateFuel C w) (H (fun _=>0))
      (A C R candidate.val pi li left (P.map (maskNat C)) acc previous next fields extra)
      (H (fun _=>0)) (A C R candidate.val pi li outLeft outRight acc previous next f extra) ∧
    VectorAccumulator.Fits R outLeft ∧ VectorAccumulator.Fits R outRight ∧ ProviderReady C R f ∧ f 106=fields 106 := by
  dsimp only
  let R:=commonReserve C w
  let P:=Normalized.structuralListPolynomialVector (canonicalGradedLabel population active) seed wins 0 candidate
  have reserve : C+2≤R:=LiteralCacheReuse.reserve_width C w
  have guards:=literal_coordinate_guards C w d population active depth mask seed wins candidate hd hC hdegree hfit hliteral
  have first:=clear_coordinate_left_run C R candidate.val pi li left (P.map (maskNat C)) acc previous next fields extra
    (by omega) hl
  have last:=literal_coordinate_run C w d population active depth pi li mask seed wins candidate hd hC hw
    hdegree hfit hfitAtom hliteral [] (by simp) acc previous next fields extra abank hready
  have bound:=WindowProvider.coordinate_substitute_budget C w P.length guards.1
  refine ⟨(first.seq last).enlarge ?_,guards.2.2.1,guards.2.2.2,coordinate_fields_ready C R [] _ _ _ fields hready,
    coordinate_fields_retained C R [] _ _ _ fields 106 (by unfold ProviderRetained;decide)⟩
  unfold literalCoordinateFuel
  dsimp only [R,P] at bound ⊢
  omega

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp

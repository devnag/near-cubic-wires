import Proof.Packets.PacketsKitSeam
import Proof.Rows.FinalWalkStep

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.MaskCoord
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces NearCubicWires.SupplierWalk
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.SupplierListSchedule
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent
noncomputable section

/-! ## The per-mask words (family level) -/

section Family
variable {q : ℕ} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (den : ℕ)

/-- One mask's coordinate vector, all `pop + 1` candidates in order. -/
def maskCoords (M : Finset (Fin occ.length)) (sample : LiveRows.Seed occ I den) : List (Ring.Poly ℕ) :=
  List.ofFn (LiveRows.coordinatePoly true occ I den M sample)

/-- The accepted term, unfolded: the masked walk-majority list coordinate. -/
theorem coords_eq (M : Finset (Fin occ.length)) (sample : LiveRows.Seed occ I den) :
    maskCoords occ I den M sample = List.ofFn (fun cand : Fin (occ.length + 1) =>
      Normalized.structuralMaskedWalkListCoordinate M
        (canonicalGradedLabel occ.length (LiveRows.bound occ I))
        (executableGradedWindow (depth := canonicalGradedDepth (LiveRows.bound occ I)) (LiveRows.bound occ I))
        gradedTerminalWindow sample cand) := rfl

/-- The mask's bits over the occurrences. -/
def maskBits (M : Finset (Fin occ.length)) : List Bool := List.ofFn (fun i : Fin occ.length => decide (i ∈ M))

/-- The walk's side bits `r_0`. -/
abbrev side : ℕ := toeplitzWalkSideBits (canonicalGradedRank occ.length (LiveRows.bound occ I))

/-- The start vertex's coordinates, framed binary (`FinalWalkStep.coordEncode`). -/
def startX (sample : LiveRows.Seed occ I den) : List Bool :=
  RepairOrdinary.frame (FinalWalkStep.coordEncode (side occ I) sample.start.1)
def startY (sample : LiveRows.Seed occ I den) : List Bool :=
  RepairOrdinary.frame (FinalWalkStep.coordEncode (side occ I) sample.start.2)

/-- One powered label: its 40 base labels, 4 bits each (160 bits). -/
def labelWord (l : PoweredMargulisLabel) : List Bool :=
  (List.ofFn l).flatMap (fun b => SignedSortKey.binary 4 b.val)

/-- The walk's `t - 1` transition labels, in order. -/
def labelsWord (sample : LiveRows.Seed occ I den) : List Bool :=
  (List.ofFn sample.transitions).flatMap labelWord

end Family

/-! ## Per request and key -/

variable (a : DecompositionAlgorithm)

/-- The masks' coordinate vectors, mask by mask. -/
def maskCoordsList : ∀ r : Request, rcKey a r → List (List (Ring.Poly ℕ))
  | .terminal, k => PEmpty.elim k
  | .sym r _ L target, k =>
      (symMasks r).map (fun M => maskCoords (symmetricFourfoldOccurrences r)
        (CyclicChoice.live (symmetricFourfoldOccurrences r) L) (symmetricListDenominator r target) M k.seed)
  | .thr r _ L target, k =>
      (thrMasks a r L target k).map (fun M => maskCoords (thresholdFourfoldOccurrences r)
        (CyclicChoice.live (thresholdFourfoldOccurrences r) L)
        (CloseoutFinalC10ThresholdRows.listDenominator a r target) M k.seed)

theorem coordsList_flatten (r : Request) (k : rcKey a r) :
    coordsListOf a r k = (maskCoordsList a r k).flatten := by
  cases r with
  | terminal => exact PEmpty.elim k
  | sym r0 four L target =>
    simp only [coordsListOf, coordsList, maskCoordsList, maskCoords, List.flatMap_def]
  | thr r0 four L target =>
    simp only [coordsListOf, coordsList, maskCoordsList, maskCoords, List.flatMap_def]

theorem vector_flatten (C w : ℕ) : ∀ pss : List (List (Ring.Poly ℕ)),
    PolyKit.vector C w pss.flatten = (pss.map (PolyKit.vector C w)).flatten
  | [] => rfl
  | ps :: pss => by
    rw [List.flatten_cons, List.map_cons, List.flatten_cons, ← vector_flatten C w pss]
    unfold PolyKit.vector PacketVector.bank
    rw [List.map_append, List.flatMap_append]

/-- **The mask loop's word algebra.** Tape 19 is the per-mask vectors, concatenated in mask order. -/
theorem coordWordK_eq {a : DecompositionAlgorithm} (K : KitShape a) (r : Request) (k : rcKey a r) :
    coordWordK K r k = ((maskCoordsList a r k).map (PolyKit.vector (K.C r) (K.w r))).flatten := by
  unfold coordWordK KitShape.word
  rw [coordsList_flatten, vector_flatten]

/-! ## The typed per-mask producer -/

end
end NearCubicWires.PacketsConstruction.MaskCoord

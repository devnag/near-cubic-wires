import Proof.Packets.PacketsRowPolySplit

/-! # Q3 F1 (i), split: level vectors → literal substitution → walk majority (typed, assembled).

Consumer: `CoordStage Y` (`Proof/Packets/PacketsRowPolySplit.lean`): tape 19 `= pad R (coordWord a r k)`, the
framed coordinate vectors `LiveRows.coordinatePoly true occ I den M seed` over the row's masks,
and tape 20 the mode bit. Paper: the walk coordinate is the majority over the walk of the
Toeplitz-hashed graded list polynomial (`paper.tex:1197-1200`, "their canonical polynomial
expansion … charged in T_prep"). Budget: one row, a fixed power of `smallSize`.

`coordinate_eq` pins the exact semantics:
`coordinatePoly true occ I den M sample cand =
  BitMajority (time ↦ literalVec M (walkSeed sample time) cand)`, where
* `walkSeed sample time` is the Toeplitz seed of the walk's `time`-th vertex;
* `levelVec seed` is the level recursion from the terminal vector (`structuralListPolynomialVector`),
  and it does NOT depend on the mask;
* `literalVec M seed` is `levelVec seed` with the masked literal atoms substituted.

Split inside `Q1 = [21, 21 + u1)` with `u1 = 2 + v1 + v2 + v3`: tape 21 holds the level vectors,
tape 22 holds the literal vectors, and `S1`, `S2`, `S3` are private regions.

* **(i.1) `LevelStage`**: `levelsOf`, the framed level vector of every walk step (seed decode,
  terminal vector, `canonicalGradedDepth` levels). This is the largest sub-stage.
* **(i.2) `LiteralStage`**: `literalsOf`, for every mask of the row and every walk step, the
  literal-substituted vector.
* **(i.3) `MajorityStage`**: for every mask, the BitMajority over walk steps; writes
  `coordWord` and the mode bit.

`CoordSplit.stage : CoordSplit Z → CoordStage Y` is PROVED here.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.SupplierListPolynomial
open NearCubicWires.SupplierListSchedule NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierWalk
noncomputable section

/-! ## The exact semantics of one coordinate vector -/

section Semantics
variable {q : ℕ} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (den : ℕ)

/-- The Toeplitz seed of the walk's `time`-th vertex. -/
def walkSeed (sample : LiveRows.Seed occ I den) (time : Fin (canonicalWalkLength den)) :=
  (toeplitzWalkEncoding (canonicalGradedRank occ.length (LiveRows.bound occ I)) (sample.vertex time)).1

/-- The graded level vector at one walk step (mask-independent). -/
def levelVec (sample : LiveRows.Seed occ I den) (time : Fin (canonicalWalkLength den)) :
    StructuralListPolynomialVector occ.length :=
  Normalized.structuralListPolynomialVector (canonicalGradedLabel occ.length (LiveRows.bound occ I))
    (walkSeed occ I den sample time)
    (executableGradedWindow (depth := canonicalGradedDepth (LiveRows.bound occ I)) (LiveRows.bound occ I))
    gradedTerminalWindow

/-- The level vector with the mask's literal atoms substituted. -/
def literalVec (M : Finset (Fin occ.length)) (sample : LiveRows.Seed occ I den)
    (time : Fin (canonicalWalkLength den)) : StructuralListPolynomialVector occ.length :=
  fun cand => Normalized.structuralGF2Substitute
    (Normalized.structuralListLiteralAtom (depth := canonicalGradedDepth (LiveRows.bound occ I)) M
      (canonicalGradedLabel occ.length (LiveRows.bound occ I)) (walkSeed occ I den sample time))
    (levelVec occ I den sample time cand)

/-- **The coordinate is the walk majority of the literal vectors.** -/
theorem coordinate_eq (M : Finset (Fin occ.length)) (sample : LiveRows.Seed occ I den)
    (cand : Fin (occ.length + 1)) :
    LiveRows.coordinatePoly true occ I den M sample cand =
      Normalized.structuralGF2BitMajority (fun time => literalVec occ I den M sample time cand) := by
  unfold LiveRows.coordinatePoly
  rfl

end Semantics

/-! ## The split shape inside `Q1` -/

namespace CoordShape


end CoordShape

namespace CoordSplit

end CoordSplit

end
end NearCubicWires.PacketsConstruction

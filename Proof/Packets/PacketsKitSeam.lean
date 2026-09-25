import Proof.Packets.PacketsPolyKit

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
noncomputable section

def codeNeed (a : DecompositionAlgorithm) (r : Request) : ℕ :=
  (canonicalGradedDepth (LiveRows.bound (r.family a).occurrences (Packets.live (r.family a))) +
    2 * (r.family a).occurrences.length + 2) ^ 2 + (r.family a).occurrences.length + relabelN a r + 1

/-- The kit parameters of every request, with the capacity facts the kit stages consume. -/
structure KitShape (a : DecompositionAlgorithm) where
  /-- code bound: masks have width `C r` -/
  C : Request → ℕ
  /-- census exponent: every register holds at most `2^(w r)` monomials -/
  w : Request → ℕ
  w_pos : ∀ r, 1 ≤ w r
  census : ∀ r, (r.smallSize a) ^ 12 ≤ 2 ^ (w r)
  codes : ∀ r, codeNeed a r ≤ C r
  cC : ℕ
  dC : ℕ
  C_le : ∀ r, C r ≤ cC * (r.smallSize a) ^ dC
  cW : ℕ
  dW : ℕ
  w_le : ∀ r, 2 ^ (w r) ≤ cW * (r.smallSize a) ^ dW

namespace KitShape
variable {a : DecompositionAlgorithm} (K : KitShape a)

/-- The kit codec of a list of polynomials of request `r`. -/
def word (r : Request) (ps : List (Ring.Poly ℕ)) : List Bool := PolyKit.vector (K.C r) (K.w r) ps

end KitShape

/-! ## The polynomial lists at the four seams -/

section Lists
variable {q : ℕ} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (den : ℕ)

/-- Coordinate vectors: mask-major, candidate-minor. -/
def coordsList (masks : List (Finset (Fin occ.length))) (sample : LiveRows.Seed occ I den) :
    List (Ring.Poly ℕ) :=
  masks.flatMap (fun M => List.ofFn (LiveRows.coordinatePoly true occ I den M sample))

end Lists

variable (a : DecompositionAlgorithm)

def coordsListOf : ∀ r : Request, rcKey a r → List (Ring.Poly ℕ)
  | .terminal, k => PEmpty.elim k
  | .sym r _ L target, k =>
      coordsList (symmetricFourfoldOccurrences r) (CyclicChoice.live (symmetricFourfoldOccurrences r) L)
        (symmetricListDenominator r target) (symMasks r) k.seed
  | .thr r _ L target, k =>
      coordsList (thresholdFourfoldOccurrences r) (CyclicChoice.live (thresholdFourfoldOccurrences r) L)
        (CloseoutFinalC10ThresholdRows.listDenominator a r target) (thrMasks a r L target k) k.seed

variable {a} (K : KitShape a)

/-- **Tape 14 (F1 → F2):** the row polynomial, one kit register. -/
def rowPolyWordK (r : Request) (k : rcKey a r) : List Bool := K.word r [(rcDecode a r k).polynomial]

/-- **Tape 19 ((i) → (ii)/(iii)):** the coordinate vectors over the row's masks. -/
def coordWordK (r : Request) (k : rcKey a r) : List Bool := K.word r (coordsListOf a r k)

end
end NearCubicWires.PacketsConstruction

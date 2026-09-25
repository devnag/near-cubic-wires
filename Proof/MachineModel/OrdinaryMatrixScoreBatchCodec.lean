import Proof.MachineModel.OrdinaryMatrixRightPaperEntry

/-! Literal raw cut input for the ordinary B.3 producer. Scalar frames are
part of the logical word; the external source is one outer `frame word`.
No scores, matrices, unary templates or sorted records are input data. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreBatch
open LocalBitMultitape SupplierPrinter SignedSortKey RepairRepresentation ExecutableInterfaces SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Cut where
  leftWeights : List ℤ
  rightWeights : List ℤ
  threshold : ℤ
  coefficient : ℤ

structure Request where
  d : ℕ
  p : ℕ
  cuts : List Cut
  lengths : ∀ c ∈ cuts,c.leftWeights.length=d ∧ c.rightWeights.length=d
  fits : ∀ c ∈ cuts,
    (∀ w ∈ c.leftWeights++c.rightWeights,w.natAbs<2^p) ∧
    c.threshold.natAbs<2^p ∧ c.coefficient.natAbs<2^p
  gateSquare : cuts.length*cuts.length ≤ rectangularInnerDimension (2^d)

def Request.U (r : Request) : ℕ := 2^r.d
def Request.Gates (r : Request) : ℕ := r.cuts.length
def Request.S (r : Request) : ℕ := r.p+natBitLength r.d+2
/-- One common coordinate width permits the paid right-coordinate swap. -/
def Request.M (r : Request) : ℕ := natBitLength (r.U+r.U)+1
def Request.Capacity (r : Request) : ℕ := rectangularInnerDimension r.U
def Request.bucketSize (r : Request) : ℕ :=
  stableCapacityBucketSize r.U r.U r.Capacity r.Gates
def Request.Buckets (r : Request) : ℕ := stableDominanceBucketCount r.U r.U r.bucketSize
def Request.Used (r : Request) : ℕ := r.Gates*r.Buckets

def signMagnitude (p : ℕ) (z : ℤ) : List Bool := decide (z<0)::binary p z.natAbs
def fields (c : Cut) : List ℤ := c.leftWeights++c.rightWeights++[c.threshold,c.coefficient]
def cutWord (p : ℕ) (c : Cut) : List Bool := (fields c).flatMap (fun z => frame (signMagnitude p z))
def header (r : Request) : List Bool := natWord r.d++natWord r.p++natWord r.Gates
def word (r : Request) : List Bool := header r++r.cuts.flatMap (cutWord r.p)
def physicalInput (r : Request) : List Bool := frame (word r)

/-- Assignment indices are in the same least-significant-bit order as `binary`. -/
def linearForm (weights : List ℤ) (assignment : ℕ) : ℤ :=
  (weights.zipIdx.map (fun wi => if assignment.testBit wi.2 then wi.1 else 0)).sum
def leftScore (r : Request) : IntMatrix r.U r.Gates := fun row gate =>
  (r.cuts.get gate).threshold-linearForm (r.cuts.get gate).leftWeights row.val
def rightScore (r : Request) : IntMatrix r.Gates r.U := fun gate column =>
  linearForm (r.cuts.get gate).rightWeights column.val
def weight (r : Request) (gate : Fin r.Gates) : ℤ := (r.cuts.get gate).coefficient

@[simp] theorem signMagnitude_length (p : ℕ) (z : ℤ) : (signMagnitude p z).length=p+1 := by
  simp [signMagnitude]

theorem cutWord_length (r : Request) (c : Cut) (hc : c ∈ r.cuts) :
    (cutWord r.p c).length=(2*r.d+2)*(2*r.p+3) := by
  obtain ⟨hl,hr⟩ := r.lengths c hc
  simp [cutWord,fields,List.length_flatMap,hl,hr]
  ring

theorem word_length (r : Request) :
    (word r).length=(header r).length+r.Gates*((2*r.d+2)*(2*r.p+3)) := by
  have hm : r.cuts.map (fun c => (cutWord r.p c).length)=
      r.cuts.map (fun _ => (2*r.d+2)*(2*r.p+3)) := by
    apply List.map_congr_left
    intro c hc
    exact cutWord_length r c hc
  simp only [word,List.length_append,List.length_flatMap]
  rw [hm]
  simp [Request.Gates]

theorem capacity (r : Request) : r.Used≤r.Capacity :=
  stableCapacityBucketDimension_le r.U r.U r.Capacity r.Gates r.gateSquare

theorem dimension_positive (r : Request) : 0<r.U := by
  exact Nat.pow_pos (by decide)

end NearCubicWires.RepairOrdinary.MatrixScoreBatch

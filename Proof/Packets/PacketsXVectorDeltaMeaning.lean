import Proof.Packets.PacketsXVectorWorkerDeltaRound
import Proof.Packets.PacketsXVectorLevelCensus

/-! Exact meaning and actual scalar ranges of the literal delta callback.
The child-cardinality input is the frozen hash-cell count, not new advice. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierListPolynomial
open NormalizedFiniteTransport

def deltaChildCard {rank depth population : Nat} (label : Fin population→BinaryVector rank)
    (seed : ToeplitzSeed rank) (level : Fin depth):=
  (hashIndexCell label seed (zeroPrefixCell rank (level.val+1))).card

theorem delta_child_card_le {rank depth population : Nat} (label : Fin population→BinaryVector rank)
    (seed : ToeplitzSeed rank) (level : Fin depth) : deltaChildCard label seed level≤population := by
  simpa only [deltaChildCard,Fintype.card_fin] using
    Finset.card_le_univ (hashIndexCell label seed (zeroPrefixCell rank (level.val+1)))

theorem delta_codes_sorted {depth population : Nat} (level : Fin depth) :
    (deltaLiteralVariableCodes (population:=population) level).Pairwise (·<·) := by
  apply List.pairwise_ofFn.mpr
  intro i j hij
  exact Nat.pair_lt_pair_right (level.val+1) hij

theorem delta_packet_exact {rank depth population : Nat} (C : Nat)
    (label : Fin population→BinaryVector rank) (seed : ToeplitzSeed rank) (wins : Fin depth→Nat)
    (level : Fin depth) (parent child : Fin (population+1)) :
    deltaPacket (deltaChildCard label seed level) (wins level) parent.val child.val
      (fun target=>(Normalized.structuralGF2ConsecutiveWindowIndicator
        (deltaLiteralVariableCodes (population:=population) level)
        (deltaChildCard label seed level-wins level) (2*wins level) target).map (maskNat C))=
      masks C (Normalized.structuralDeltaFactor label seed wins level parent child) := by
  unfold deltaPacket Normalized.structuralDeltaFactor deltaChildCard
  dsimp only
  split <;> rename_i h <;> rw [h] <;> rfl

end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp

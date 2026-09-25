import Proof.Packets.Ring
import Proof.Packets.Normalizer
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace RCFive.PacketBounds
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierWalkBridge
open NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

theorem fold_max_member (xs : List Nat) (z x : Nat) (hx : x ∈ xs) : x ≤ xs.foldl max z := by
  induction xs generalizing z with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · have aux : ∀ (ys : List Nat) (z : Nat), z ≤ ys.foldl max z := by
        intro ys
        induction ys with
        | nil => simp
        | cons y ys ih => intro z; exact (Nat.le_max_left z y).trans (ih (max z y))
      exact (Nat.le_max_right z x).trans (aux ys (max z x))
    · exact ih (max z y) hx

theorem degree_bound (a : DecompositionAlgorithm) (r : Request)
    (row : Packets.Row (r.family a).occurrences r.liveScale) (h : row ∈ (r.family a).rows) :
    row.degree ≤ r.degree a :=
  fold_max_member _ 0 _ (List.mem_map.mpr ⟨row,h,rfl⟩)

theorem occurrence_power (a : DecompositionAlgorithm) (r : Request) :
    ((r.family a).occurrences.length+2)^(r.degree a+1) ≤ r.smallSize a := by
  dsimp only [Request.smallSize]
  generalize (2:Nat)^(Packets.live (r.family a)).card = livePower
  generalize (2:Nat)^(canonicalWalkLength (r.denominator a)) = walkPower
  omega

theorem positive (a : DecompositionAlgorithm) (r : Request) : 1 ≤ r.smallSize a := by
  dsimp only [Request.smallSize]
  generalize (2:Nat)^(Packets.live (r.family a)).card = livePower
  generalize (2:Nat)^(canonicalWalkLength (r.denominator a)) = walkPower
  omega

end
end RCFive.PacketBounds

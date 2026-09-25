import Proof.Packets.PacketsLowerStage
import Proof.Packets.PacketsLowerVec

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
noncomputable section

theorem relabelN_eq (a : DecompositionAlgorithm) (r : Request) : relabelN a r = childTotal a r := by
  have e : relabelN a r + 2 = alphabet a r := rfl
  have h := alphabet_eq a r
  omega

theorem codes_le (a : DecompositionAlgorithm) (r : Request) : codeNeed a r ≤ kitC a r := by
  have h := codeBound_le_kitC a r
  have e : codeNeed a r = codeBound a r := by
    unfold codeNeed codeBound
    rw [relabelN_eq]
    rfl
  omega

/-- **The kit shape**, from the typed inputs of `wStage`. -/
def kitShapePG (a : DecompositionAlgorithm) : KitShape a where
  C := kitC a
  w := wOf a
  w_pos := w_pos a
  census := census a
  codes := codes_le a
  cC := (kitCStage a).coefficient + 7
  dC := (kitCStage a).degree + 1
  C_le := fun r => by
    have := (kitCStage a).value_bound r
    omega
  cW := 10 ^ 12
  dW := 24
  w_le := w_le a

/-- Route A's code bound. -/
theorem kitC_route (a : DecompositionAlgorithm) (r : Request) :
    (258 * (r.family a).occurrences.length + 2) ^ 2 ≤ (kitShapePG a).C r :=
  sq_le_kitC a r

def lowerMetaK (a : DecompositionAlgorithm) (qS : UnaryStage a (fun r => r.q)) (degS : UnaryStage a (degree a))
    (tupS : UnaryStage a (tupleWork a)) (walkS : UnaryStage a (walkLength a)) :
    LowerKit.LowerMeta a (kitShapePG a) :=
  let m := lowerMetaPG a qS degS tupS walkS
  { tapes := m.tapes
    tapes_ge := m.tapes_ge
    states := m.states
    machine := m.machine
    cost := m.cost
    cM := m.cM
    dM := m.dM
    cost_le := m.cost_le
    cap := m.cap
    cK := m.cK
    dK := m.dK
    cap_le := m.cap_le
    cap_ge := m.cap_ge
    run := m.run }

end
end NearCubicWires.PacketsGlue.RequestMeta


import Proof.Packets.PacketsCircBound
import Proof.Packets.PacketsCursorFam
import Proof.Packets.PacketsHolesSplit
import Proof.Packets.PacketsKeysDegree
import Proof.Packets.PacketsKeysPrepFam
import Proof.Packets.PacketsKeysTuple

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.Residual
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
open NearCubicWires.PacketsGlue.RequestMeta
noncomputable section

section Free
variable (a : DecompositionAlgorithm)

/-- The shared request stages. -/
def cutS := NearCubicWires.PacketsMeta.cutoffStage a
def thrSelS := NearCubicWires.PacketsMeta.thrSelStage a
def seedS := NearCubicWires.PacketsMeta.Seed.seedCountStage a
def bigS := bigStage a (qStage a) (NearCubicWires.PacketsKeys.Degree.degStage a (cutS a) (thrSelS a))
  (NearCubicWires.PacketsKeys.Tuple.tupleStage a (cutS a)) (walkStage a (cutS a) (thrSelS a))
def fieldWS := fieldWidthStage a (seedS a) (NearCubicWires.PacketsKeys.Native.coordStage a) (cutS a)
def rowsS := RowsInit.Count.rowsCountStage a (cutS a) (seedS a) (thrSelS a)
  (NearCubicWires.PacketsKeys.Native.symSelStage a)

def setupFam : SetupFam a where
  base := bigOf a
  small_le_base := small_le_big a
  baseC := 4
  baseD := 2
  base_le := big_le a
  c0 := 2
  D0 := 1
  u := fun _ D => (setupVecR a (fieldWS a) (rowsS a) (bigS a)).extra + D + 3
  need := needR a (fieldWS a) (rowsS a) (bigS a)
  need_pb := PB.of_le _ _ (needR_le a (fieldWS a) (rowsS a) (bigS a))
  setup := setupFamField a (fieldWS a) (rowsS a) (bigS a) 4 2 (big_le a)

/-- **The cursor hole.** -/
theorem cursorFam_at : Nonempty (CursorFam a) :=
  Cursor.cursorFam_nonempty (CircBound.circBoundStage a) (bigS a) (small_le_big a) (PB.of_le 4 2 (big_le a))

theorem freeHoles_at : FreeHoles a := by
  obtain ⟨cur⟩ := cursorFam_at a
  exact ⟨(NearCubicWires.PacketsKeys.Prep.prepFam a, cur, setupFam a)⟩

end Free

theorem freeHoles : ∀ a, FreeHoles a := freeHoles_at

end
end NearCubicWires.PacketsConstruction.Residual

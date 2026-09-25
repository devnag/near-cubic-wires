import Proof.Packets.PacketsCombineThrMetaPG
import Proof.Packets.PacketsCoordFill
import Proof.Packets.PacketsHolesSplit
import Proof.Packets.PacketsKeyWords
import Proof.Packets.PacketsKeysDegree
import Proof.Packets.PacketsKeysTuple
import Proof.Packets.PacketsMetaKeyWords
import Proof.Packets.PacketsSeedKey
import Proof.Packets.PacketsVecLen

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.Residual.KH
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction NearCubicWires.PacketsConstruction.Residual
open NearCubicWires.PacketsCombine
open NearCubicWires.PacketsGlue.RequestMeta
noncomputable section

section Stages
variable (a : DecompositionAlgorithm)

def cut := NearCubicWires.PacketsMeta.cutoffStage a
def thrSel := NearCubicWires.PacketsMeta.thrSelStage a
def degS := NearCubicWires.PacketsKeys.Degree.degStage a (cut a) (thrSel a)
def tupS := NearCubicWires.PacketsKeys.Tuple.tupleStage a (cut a)
def walkS := walkStage a (cut a) (thrSel a)
def wS : UnaryStage a (wOf a) := wStage a (qStage a) (degS a) (tupS a) (walkS a)
def bigS : UnaryStage a (bigOf a) := bigStage a (qStage a) (degS a) (tupS a) (walkS a)
def lsS := NearCubicWires.PacketsSeed.labelStage a (walkS a)
def ssS := NearCubicWires.PacketsSeed.sideWordStage a

/-- **The mask cell's middle words** at `kitShapePG a`, the mask bits a typed input. -/
def mid (maskS : KeyStage a (fun r k j => (maskBitsList a r k).getD j [])) : MidParts a (kitShapePG a) where
  bS := KeyWord.ofWord (touchStage a).toWord
  popS := KeyWord.ofWord (popStage a).toWord
  cS := KeyWord.ofWord (kitCStage a).toWord
  rootS := KeyWord.ofWord (rootStage a).toWord
  maskS := maskS
  labelsS := NearCubicWires.PacketsSeed.labelsKey (lsS a) (ssS a)
  nS := KeyWord.ofWord (NearCubicWires.PacketsSeed.nWordStage a (walkS a))
  xS := NearCubicWires.PacketsSeed.startXKey (lsS a) (ssS a)
  yS := NearCubicWires.PacketsSeed.startYKey (lsS a) (ssS a)
  wS := KeyWord.ofWord (wS a).toWord
  termS := KeyWord.ofWord (NearCubicWires.PacketsSeed.termStage a (wS a))

/-- The mode bit word (`symBit = modeBit` by cases). -/
def modeKW : KeyWord a (fun r _ => [modeBit r]) :=
  NearCubicWires.PacketsSeed.KeyWord.congrV (KeyWord.ofWord (modeWordStage a)) (fun r _ => by cases r <;> rfl)

/-- **The coordinate hole**, the mask bits and the loop counter typed inputs. -/
theorem coord_at (maskS : KeyStage a (fun r k j => (maskBitsList a r k).getD j []))
    (cntS : KeyWord a (fun r k => CompareMachine.word (maskCount a r k))) : Nonempty (CoordFam a (kitShapePG a)) :=
  Donor.coordFam_nonempty (fun r => kitC_route a r) ⟨mid a maskS, NearCubicWires.PacketsSeed.appendStage⟩
    (KeyWord.ofWord (NearCubicWires.PacketsSeed.lenStage a (wS a)).toWord) (modeKW a) cntS (bigS a) (small_le_big a)
    (PB.of_le 4 2 (big_le a))

def thrAt : ThrMeta a (kitShapePG a) :=
  NearCubicWires.PacketsCombine.Asm.thrMetaPG a (cut a) (wS a) (NearCubicWires.PacketsMeta.Keys.primeW a)
    (NearCubicWires.PacketsMeta.Keys.resW a) (NearCubicWires.PacketsMeta.Keys.primeW_thr (a := a))
    (NearCubicWires.PacketsMeta.Keys.resW_thr (a := a))

def lowerAt : LowerKit.LowerMeta a (kitShapePG a) := lowerMetaK a (qStage a) (degS a) (tupS a) (walkS a)

end Stages

theorem kHoles_of (maskS : ∀ a, KeyStage a (fun r k j => (maskBitsList a r k).getD j []))
    (cntS : ∀ a, KeyWord a (fun r k => CompareMachine.word (maskCount a r k)))
    (symM : ∀ a, SymMeta a (kitShapePG a)) : ∀ a, KHoles a := fun a => by
  obtain ⟨cf⟩ := coord_at a (maskS a) (cntS a)
  exact ⟨kitShapePG a, ⟨(cf, symM a, thrAt a, lowerAt a)⟩⟩

end
end NearCubicWires.PacketsConstruction.Residual.KH

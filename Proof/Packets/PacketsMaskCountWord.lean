import Proof.Packets.PacketsMaskCountJoin
import Proof.Packets.PacketsKeysSymMask
import Proof.Packets.PacketsCombineThrMetaPG
import Proof.Packets.PacketsMetaKeyWords

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsMaskCount
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrime NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction NearCubicWires.PacketsConstruction.Residual
open NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.PacketsKeys.Stage
noncomputable section

variable (a : DecompositionAlgorithm)

/-- **THR mask count**: one mask per residue digit of the key's prime. -/
theorem thr_count (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target) :
    maskCount a (.thr r four L target) k = modulusDigitCount k.prime.val := by
  unfold maskCount MaskCoord.maskCoordsList PacketsConstruction.thrMasks
  rw [List.length_map, List.length_ofFn]

/-- **The SYM half**: `CompareMachine.word (#circuits)` on SYM requests. -/
def symCount : KeyWordOn a IsSym (fun r k => CompareMachine.word (maskCount a r k)) :=
  KeyWordOn.congrOn
    (KeyWordOn.ofKeyWord IsSym (KeyWord.ofWord ((PacketsKeys.Native.circuitsStage a).thenWordP cmpWordMap 6 1 cmp_cost)))
    (by
      intro r hp k _
      cases r with
      | terminal => exact hp.elim
      | thr _ _ _ _ => exact hp.elim
      | sym r0 four L target =>
        show CompareMachine.word (PacketsKeys.Native.nCirc (.sym r0 four L target)) =
          CompareMachine.word (maskCount a (.sym r0 four L target) k)
        rw [PacketsKeys.Stage.sym_count a r0 four L target k]
        rfl)

def thrCount (cutS : UnaryStage a (cutoffOf a)) {vP : ∀ r : Request, rcKey a r → List Bool}
    (primeW : KeyWord a vP)
    (hP : ∀ (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : ℕ)
      (k : RCFive.RowKeys.ThrKey a r L target), vP (.thr r four L target) k = List.replicate k.prime.val true) :
    KeyWordOn a IsThr (fun r k => CompareMachine.word (maskCount a r k)) :=
  KeyWordOn.ofThrWord
    ((PacketsCombine.Asm.thrDWord cutS primeW hP).thenWord cmpWordMap (24 * PacketsCombine.Asm.bigC cutS)
      (PacketsCombine.Asm.bigD cutS) (by
        intro r four L target k _
        have hs := PacketsCombine.Asm.thr_scalars cutS r four L target k
        have hc := cmp_cost (PacketsCombine.thrD k)
        rw [pow_one] at hc
        rw [Nat.mul_assoc]
        omega))
    (fun r four L target k => by
      rw [thr_count a r four L target k]
      rfl)

def maskCountWord : KeyWord a (fun r k => CompareMachine.word (maskCount a r k)) :=
  (symCount a).join (thrCount a (PacketsMeta.cutoffStage a) (PacketsMeta.Keys.primeW a)
    (PacketsMeta.Keys.primeW_thr (a := a)))

end
end NearCubicWires.PacketsMaskCount


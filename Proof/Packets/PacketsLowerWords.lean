import Proof.Packets.PacketsKitBoot
import Proof.Packets.PacketsXMajorityCompletePacketAtomsJoinRun

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.LowerWords
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.ProjectionNormalization
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
noncomputable section

/-! ## The join's entry words outside the arena (one small lemma per tape) -/

theorem join_30 (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) :
    MajorityComplete.PacketAtomsJoin.input C R cs P 30 = List.replicate R false := ZeroPadding.pad_zero _

theorem join_31 (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) :
    MajorityComplete.PacketAtomsJoin.input C R cs P 31 = List.replicate R false := ZeroPadding.pad_zero _

theorem join_36 (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) :
    MajorityComplete.PacketAtomsJoin.input C R cs P 36 = ZeroPadding.pad R (CloseoutRowsRawPairSeek.cacheWord cs) := rfl

theorem join_37 (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) :
    MajorityComplete.PacketAtomsJoin.input C R cs P 37 = List.replicate R false := ZeroPadding.pad_zero _

theorem join_38 (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) :
    MajorityComplete.PacketAtomsJoin.input C R cs P 38 = List.replicate R false := ZeroPadding.pad_zero _

theorem join_39 (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) :
    MajorityComplete.PacketAtomsJoin.input C R cs P 39 = List.replicate R false := ZeroPadding.pad_zero _

theorem join_40 (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) :
    MajorityComplete.PacketAtomsJoin.input C R cs P 40 = [] := rfl

theorem join_41 (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) :
    MajorityComplete.PacketAtomsJoin.input C R cs P 41 = ZeroPadding.pad R (CompareMachine.word 0) := ZeroPadding.pad_zero _

theorem join_42 (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) :
    MajorityComplete.PacketAtomsJoin.input C R cs P 42 = [] := rfl

theorem join_43 (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) :
    MajorityComplete.PacketAtomsJoin.input C R cs P 43 = List.replicate R false := ZeroPadding.pad_zero _

theorem join_44 (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) :
    MajorityComplete.PacketAtomsJoin.input C R cs P 44 = ZeroPadding.pad R (CompareMachine.word 0) := ZeroPadding.pad_zero _

theorem join_45 (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) :
    MajorityComplete.PacketAtomsJoin.input C R cs P 45 = ZeroPadding.pad R (CompareMachine.word cs.length) := ZeroPadding.pad_zero _

theorem join_46 (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) :
    MajorityComplete.PacketAtomsJoin.input C R cs P 46 = PacketVector.payload R (P.map (NormalizedFiniteTransport.maskNat C)) := rfl

theorem join_47 (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) :
    MajorityComplete.PacketAtomsJoin.input C R cs P 47 = PacketVector.count R (P.map (NormalizedFiniteTransport.maskNat C)) := rfl

theorem join_48 (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) :
    MajorityComplete.PacketAtomsJoin.input C R cs P 48 = [] := rfl

theorem join_49 (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) :
    MajorityComplete.PacketAtomsJoin.input C R cs P 49 = [] := rfl

theorem join_50 (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) :
    MajorityComplete.PacketAtomsJoin.input C R cs P 50 = [] := rfl

theorem join_51 (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) :
    MajorityComplete.PacketAtomsJoin.input C R cs P 51 = [] := rfl

theorem join_52 (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) :
    MajorityComplete.PacketAtomsJoin.input C R cs P 52 = [] := rfl

theorem join_53 (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) :
    MajorityComplete.PacketAtomsJoin.input C R cs P 53 = [] := rfl

theorem join_54 (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) :
    MajorityComplete.PacketAtomsJoin.input C R cs P 54 = [] := rfl

theorem join_55 (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) :
    MajorityComplete.PacketAtomsJoin.input C R cs P 55 = [] := rfl

theorem join_56 (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) :
    MajorityComplete.PacketAtomsJoin.input C R cs P 56 = [] := rfl

theorem join_57 (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) :
    MajorityComplete.PacketAtomsJoin.input C R cs P 57 = [] := rfl

theorem join_arena (C R : ℕ) (cs : List CloseoutRowsRawPairSeek.Pair) (P : Ring.Poly ℕ) (hR : 1 ≤ R)
    (i : Fin 34) :
    MajorityComplete.PacketAtomsJoin.input C R cs P
        (Fin.castAdd 12 (MajorityComplete.PacketAtoms.arithmeticSlots i)) =
      ReusableArithmetic.state C R [] [] i := by
  have h := MajorityComplete.PacketAtoms.arithmetic_words C R id cs [] hR i
  have hne : (MajorityComplete.PacketAtoms.arithmeticSlots i) ≠ 40 := by
    intro he
    have hv := congrArg Fin.val he
    unfold MajorityComplete.PacketAtoms.arithmeticSlots at hv
    split_ifs at hv <;> simp at hv <;> omega
  simp only [MajorityComplete.PacketAtomsJoin.input, Fin.append_left, IdentityAtomMaterialize.input,
    Function.update_of_ne hne]
  exact h

end
end NearCubicWires.PacketsConstruction.LowerWords

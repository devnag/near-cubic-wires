import Proof.Packets.PacketsXOrderedPacketStep
import Proof.Packets.VectorChildLookup

/-! Exact natural-code packet lookup into the right operand. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.OrderedPacketStep
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds

theorem fetch_right (C w : Nat) (ps : List (Ring.Poly Nat)) (i : Fin ps.length)
    (left acc : Ring.Poly Nat) (hl : acc.length≤2^w) (hps : ∀P∈ps,P.length≤2^w) :
    Step VectorChildLookup.machine (ArithmeticLookup.budget (commonReserve C w) i.val)
      (ArithmeticLookup.H 0) (A C (commonReserve C w) i.val left acc ps)
      (ArithmeticLookup.H 0) (A C (commonReserve C w) i.val left ps[i.val] ps) := by
  let masks:=ps.map (List.map (maskNat C))
  let ix : Fin masks.length:=⟨i.val,by simpa only [masks,List.length_map] using i.isLt⟩
  have hfit:=bank_fit C w ps hps
  have leftfit:=(SubstitutionCensus.packet_fits C w _ (SubstitutionCensus.mask_width C acc)
    (by simpa only [List.length_map] using hl)).1
  have selectedfit:=hfit masks[ix.val] (List.getElem_mem ix.isLt)
  have hpre : (PacketVector.bank (commonReserve C w) (masks.take ix.val)).length=
      2*ix.val*commonReserve C w := by
    rw [PacketVector.bank_length _ _ (fun P hP=>hfit P (List.mem_of_mem_take hP)),List.length_take]
    rw [Nat.min_eq_left (Nat.le_of_lt ix.isLt)]
  have run:=VectorChildLookup.run C (commonReserve C w) ix.val
    (left.map (maskNat C)) (acc.map (maskNat C)) masks[ix.val]
    (PacketVector.bank (commonReserve C w) (masks.take ix.val))
    (PacketVector.bank (commonReserve C w) (masks.drop (ix.val+1))) hpre leftfit.1
    (by simpa only [CompareMachine.word,List.length_cons,List.length_replicate] using leftfit.2)
    selectedfit.1
    (by simpa only [CompareMachine.word,List.length_cons,List.length_replicate] using selectedfit.2)
  dsimp only at run
  change Step _ _ _ (VectorChildLookup.tapes _ _ _ _ _
    (PacketVector.bank _ (masks.take ix.val)++PacketVector.payload _ masks[ix.val]++
      PacketVector.count _ masks[ix.val]++PacketVector.bank _ (masks.drop (ix.val+1)))) _
    (VectorChildLookup.tapes _ _ _ _ _
    (PacketVector.bank _ (masks.take ix.val)++PacketVector.payload _ masks[ix.val]++
      PacketVector.count _ masks[ix.val]++PacketVector.bank _ (masks.drop (ix.val+1)))) at run
  rw [←PacketVector.bank_split _ masks ix] at run
  have hh : VectorChildLookup.heads=ArithmeticLookup.H 0:=by
    funext j;fin_cases j <;>rfl
  rw [hh] at run
  have ht (l r : List (List Bool)) (src : List Bool) :
      VectorChildLookup.tapes C (commonReserve C w) i.val l r src=
        ArithmeticLookup.A C (commonReserve C w) i.val l r src := by
    funext j;fin_cases j <;>rfl
  dsimp only [ix] at run
  rw [ht,ht] at run
  simpa only [A,bank,masks,List.getElem_map,ArithmeticLookup.budget] using run

end PCJ9eff70d512234a4c_Fixed.Materializer.OrderedPacketStep

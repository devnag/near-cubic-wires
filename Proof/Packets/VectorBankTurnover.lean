import Proof.Packets.PacketVector
import Proof.Packets.VectorControllerData

/-! Exact vector semantics of the physical double-buffer transfer. Both banks
contain the same number of fixed-size packet entries. The copied next bank is
reset to a vector of zero polynomials, with every tape cursor restored. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBankTurnover
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

def rows (R : Nat) (ns ps : List PacketVector.Packet) : List VectorTransfer.Pair :=
  (ns.zip ps).map (fun p=>((PacketVector.payload R p.1,PacketVector.count R p.1),
    (PacketVector.payload R p.2,PacketVector.count R p.2)))

theorem rows_length (R : Nat) (ns ps : List PacketVector.Packet) (he : ns.length=ps.length) :
    (rows R ns ps).length=ns.length := by simp [rows,he]

theorem source_bytes (R : Nat) (ns ps : List PacketVector.Packet) (he : ns.length=ps.length) :
    VectorTransfer.sourceBytes (rows R ns ps)=PacketVector.bank R ns := by
  calc
    _=((ns.zip ps).map Prod.fst).flatMap (PacketVector.entry R) := by
      simp only [rows,VectorTransfer.sourceBytes,List.flatMap_map,PacketVector.entry]
    _=_ := by rw [List.map_fst_zip he.le];rfl

theorem target_bytes (R : Nat) (ns ps : List PacketVector.Packet) (he : ns.length=ps.length) :
    VectorTransfer.targetBytes (rows R ns ps)=PacketVector.bank R ps := by
  calc
    _=((ns.zip ps).map Prod.snd).flatMap (PacketVector.entry R) := by
      simp only [rows,VectorTransfer.targetBytes,List.flatMap_map,PacketVector.entry]
    _=_ := by rw [List.map_snd_zip he.ge];rfl

theorem rows_fits (R : Nat) (ns ps : List PacketVector.Packet)
    (hn : ∀ P∈ns,PacketVector.Fits R P) (hp : ∀ P∈ps,PacketVector.Fits R P) :
    VectorTransfer.Fits R (rows R ns ps) := by
  intro row hr
  obtain ⟨⟨P,Q⟩,hPQ,rfl⟩:=List.mem_map.mp hr
  have hm:=List.of_mem_zip hPQ
  exact ⟨PacketVector.payload_length (hn P hm.1),PacketVector.count_length (hn P hm.1),
    PacketVector.payload_length (hp Q hm.2),PacketVector.count_length (hp Q hm.2)⟩

theorem zero_entry (R : Nat) (hr : 1≤R) : PacketVector.entry R []=List.replicate (2*R) false := by
  unfold PacketVector.entry PacketVector.payload PacketVector.count
  simp only [List.flatten_nil,List.length_nil,VectorAccumulator.zero_count R hr]
  simp only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]
  rw [←List.replicate_add,show R+R=2*R by omega]

theorem zero_bank (R N : Nat) (hr : 1≤R) :
    PacketVector.bank R (List.replicate N [])=List.replicate (N*(2*R)) false := by
  induction N with
  | zero=>simp [PacketVector.bank]
  | succ N ih=>
    simp only [List.replicate_succ,PacketVector.bank,List.flatMap_cons]
    change PacketVector.entry R []++PacketVector.bank R (List.replicate N [])=_
    rw [zero_entry R hr,ih,←List.replicate_add,show 2*R+N*(2*R)=(N+1)*(2*R) by ring]

theorem run (R : Nat) (ns ps : List PacketVector.Packet) (he : ns.length=ps.length) (hr : 1≤R)
    (hn : ∀ P∈ns,PacketVector.Fits R P) (hp : ∀ P∈ps,PacketVector.Fits R P) :
    Step VectorTransfer.machine (VectorTransfer.budget R ns.length) (VectorTransfer.heads 0 0)
      (VectorTransfer.tapes R ns.length (PacketVector.bank R ns) (PacketVector.bank R ps))
      (VectorTransfer.heads 0 0)
      (VectorTransfer.tapes R ns.length (PacketVector.bank R (List.replicate ns.length [])) (PacketVector.bank R ns)) := by
  have h:=VectorTransfer.run R (rows R ns ps) [] [] [] [] (rows_fits R ns ps hn hp)
  simpa only [List.length_nil,List.nil_append,List.append_nil,rows_length R ns ps he,
    source_bytes R ns ps he,target_bytes R ns ps he,zero_bank R ns.length hr] using h

end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBankTurnover

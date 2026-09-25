import Proof.Packets.PacketVector

/-! Exact ordered time prefixes and allocated suffixes of a packet transcript. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PacketTranscript
open NearCubicWires

def prefixBank (R : Nat) (rows : Nat→List PacketVector.Packet) (n : Nat) :=
  (List.range n).flatMap (fun i=>PacketVector.bank R (rows i))
theorem prefix_zero (R : Nat) (rows : Nat→List PacketVector.Packet) : prefixBank R rows 0=[] := rfl

theorem prefix_succ (R : Nat) (rows : Nat→List PacketVector.Packet) (n : Nat) :
    prefixBank R rows (n+1)=prefixBank R rows n++PacketVector.bank R (rows n) := by
  simp only [prefixBank,List.range_succ,List.flatMap_append,List.flatMap_singleton]

theorem prefix_length (R N : Nat) (rows : Nat→List PacketVector.Packet)
    (hlen : ∀i,(rows i).length=N) (hfit : ∀i,∀P∈rows i,PacketVector.Fits R P) (n : Nat) :
    (prefixBank R rows n).length=n*(N*(2*R)) := by
  induction n with
  | zero=>simp [prefix_zero]
  | succ n ih=>
    rw [prefix_succ,List.length_append,ih,PacketVector.bank_length R (rows n) (hfit n),hlen]
    ring

theorem remaining_split (N i stride : Nat) (hi : i<N) :
    List.replicate ((N-i)*stride) false=
      List.replicate stride false++List.replicate ((N-(i+1))*stride) false := by
  rw [←List.replicate_add]
  congr 1
  have h : N-i=N-(i+1)+1 := by omega
  rw [h]
  ring

end PCJ9eff70d512234a4c_Fixed.Materializer.PacketTranscript

import Proof.Packets.PacketVector

/-! Exact bytes and capacity invariants for replacing a dense packet entry. -/
set_option autoImplicit false
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PacketVector
open NearCubicWires.RepairOrdinary NearCubicWires.RepairSource.VerifierDecoding

theorem bank_set (R : Nat) (ps : List Packet) (i : Nat) (P : Packet) (hi : i<ps.length) :
    bank R (ps.set i P)=bank R (ps.take i)++payload R P++count R P++bank R (ps.drop (i+1)) := by
  rw [List.set_eq_take_append_cons_drop,if_pos hi]
  simp only [bank,List.flatMap_append,List.flatMap_cons,entry,List.append_assoc]

theorem fits_set (R : Nat) (ps : List Packet) (i : Nat) (P : Packet)
    (hs : ∀Q∈ps,Fits R Q) (hp : Fits R P) : ∀Q∈ps.set i P,Fits R Q := by
  intro Q hQ
  rcases List.mem_or_eq_of_mem_set hQ with h|rfl
  · exact hs Q h
  · exact hp

theorem empty_fits (R : Nat) (hR : 1≤R) : Fits R [] := by
  simp [Fits,CompareMachine.word,hR]

theorem empty_entry (R : Nat) (hR : 1≤R) : entry R []=List.replicate (2*R) false := by
  have one : ZeroPadding.pad R (CompareMachine.word 0)=List.replicate R false := by
    change ZeroPadding.pad R (List.replicate 1 false)=_
    rw [Rewind.Workspace.pad_zeros,Nat.max_eq_left hR]
  simp only [entry,payload,count,List.flatten_nil,List.length_nil,one]
  simp [ZeroPadding.pad,two_mul]

theorem empty_bank (R C : Nat) (hR : 1≤R) :
    bank R (List.replicate C [])=List.replicate (C*(2*R)) false := by
  induction C with
  | zero=>simp [bank]
  | succ C ih=>
    rw [List.replicate_succ]
    change entry R []++bank R (List.replicate C [])=_
    rw [empty_entry R hR,ih,←List.replicate_add]
    congr 1
    ring

end PCJ9eff70d512234a4c_Fixed.Materializer.PacketVector

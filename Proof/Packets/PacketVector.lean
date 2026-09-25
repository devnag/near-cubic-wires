import Proof.Packets.PacketBankLookup
import Proof.Packets.PacketBankStore

/-! Actual indexed access and append for materialized polynomial vectors.
Each resident entry stores the mask bank followed by its physical unary count,
with the same paid R-bit reserve used by the reusable arithmetic workers. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PacketVector
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

abbrev Packet := List (List Bool)
def payload (R : Nat) (P : Packet) : List Bool := ZeroPadding.pad R P.flatten
def count (R : Nat) (P : Packet) : List Bool := ZeroPadding.pad R (CompareMachine.word P.length)
def Fits (R : Nat) (P : Packet) : Prop := P.flatten.length≤R ∧ (CompareMachine.word P.length).length≤R
def entry (R : Nat) (P : Packet) : List Bool := payload R P++count R P
def bank (R : Nat) (ps : List Packet) : List Bool := ps.flatMap (entry R)

theorem payload_length {R : Nat} {P : Packet} (h : Fits R P) : (payload R P).length=R := by
  simp only [payload,ZeroPadding.pad_length,Nat.max_eq_left h.1]
theorem count_length {R : Nat} {P : Packet} (h : Fits R P) : (count R P).length=R := by
  simp only [count,ZeroPadding.pad_length,Nat.max_eq_left h.2]
theorem entry_length {R : Nat} {P : Packet} (h : Fits R P) : (entry R P).length=2*R := by
  simp only [entry,List.length_append,payload_length h,count_length h]
  omega

theorem bank_length (R : Nat) (ps : List Packet) (h : ∀ P∈ps,Fits R P) :
    (bank R ps).length=2*ps.length*R := by
  induction ps with
  | nil=>simp [bank]
  | cons P ps ih=>
    have hP:=entry_length (h P (by simp))
    have hps:=ih (fun Q hQ=>h Q (by simp [hQ]))
    simp only [bank,List.flatMap_cons,List.length_append,List.length_cons] at *
    nlinarith

theorem bank_append (R : Nat) (ps qs : List Packet) : bank R (ps++qs)=bank R ps++bank R qs :=
  List.flatMap_append

theorem bank_split (R : Nat) (ps : List Packet) (i : Fin ps.length) :
    bank R ps=bank R (ps.take i.val)++payload R ps[i.val]++count R ps[i.val]++
      bank R (ps.drop (i.val+1)) := by
  have h : ps.take i.val++ps[i.val]::ps.drop (i.val+1)=ps := by
    rw [List.getElem_cons_drop,List.take_append_drop]
  conv_lhs=>rw [←h]
  simp only [bank,List.flatMap_append,List.flatMap_cons,entry,List.append_assoc]

end PCJ9eff70d512234a4c_Fixed.Materializer.PacketVector

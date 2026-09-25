import Proof.Packets.PacketsXVectorWorkerReset
import Proof.Packets.PacketsXVectorWorkerCommitNat

/-! Full parent body: paid counter reset, actual child execution, indexed
parent write, and accumulator erasure. The counted child run is a composable
Step from child_loop_run, with no extra tape or scalar oracle. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def parentH (mh : Fin 222→Nat) : Fin 297→Nat:=Fin.addCases (m:=296) (n:=1) (motive:=fun _=>Nat) (H mh) (fun _=>1)
def parentA (C R N ci pi li : Nat) (left right acc : PacketVector.Packet) (previous next : List Bool)
    (fields : Fin 222→List Bool) (extra : Fin 32→List Bool) : Fin 297→List Bool :=
  Fin.addCases (m:=296) (n:=1) (motive:=fun _=>List Bool)
    (A C R ci pi li left right acc previous next fields extra) (fun _=>ZeroPadding.pad R (CompareMachine.word N))

attribute [local irreducible] resetChild children commit parentBody

theorem parent_body_run {s : Nat} (provider : Machine 256 s) (C R N ci li E : Nat)
    (ns : List (Ring.Poly Nat)) (i : Fin ns.length) (answer : Ring.Poly Nat)
    (left right left' right' : PacketVector.Packet) (previous : List Bool)
    (mh : Fin 222→Nat) (fields fields' : Fin 222→List Bool) (extra extra' : Fin 32→List Bool)
    (hc : ci+1≤R) (hns : ∀P∈ns,VectorAccumulator.Fits R (masks C P))
    (ha : VectorAccumulator.Fits R (masks C answer))
    (hchildren : Step (children provider) E (parentH mh)
      (parentA C R N 0 i.val li left right [] previous (vectorBank C R ns) fields extra)
      (parentH mh) (parentA C R N N i.val li left' right' (masks C answer)
        previous (vectorBank C R ns) fields' extra')) :
    Step (parentBody provider) (E+VectorParentCommit.budget R i.val+2*R+8) (parentH mh)
      (parentA C R N ci i.val li left right [] previous (vectorBank C R ns) fields extra)
      (parentH mh) (parentA C R N N i.val li left' right' []
        previous (vectorBank C R (ns.set i.val answer)) fields' extra') := by
  have first:=(reset_child_run C R ci i.val li left right [] previous (vectorBank C R ns) mh fields extra hc).embed
    (fun _ : Fin 1=>1) (fun _ : Fin 1=>ZeroPadding.pad R (CompareMachine.word N))
  have last:=(commit_vector_nat C R N li ns i left' right' answer previous mh fields' extra' hns ha).embed
    (fun _ : Fin 1=>1) (fun _ : Fin 1=>ZeroPadding.pad R (CompareMachine.word N))
  have joined:=first.seq (hchildren.seq last)
  have fuel : (2*R+6)+1+(E+1+VectorParentCommit.budget R i.val)=E+VectorParentCommit.budget R i.val+2*R+8 := by omega
  rw [fuel] at joined
  simpa only [parentBody,parentH,parentA] using joined

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp

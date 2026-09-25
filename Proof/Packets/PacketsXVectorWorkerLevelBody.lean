import Proof.Packets.PacketsXVectorWorkerLevelLoop
import Proof.Packets.PacketsXVectorWorkerParentReset
import Proof.Packets.PhysicalAppendAssociativity

/-! One complete actual level body: paid numeric/cache preparation, parent
counter reset, all parent computations, and physical double-buffer turnover. -/
set_option autoImplicit false
set_option maxHeartbeats 950000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section
attribute [local irreducible] prepareLevel resetParent parents transfer levelBody

theorem level_body_run {s l : Nat} (provider : Machine 256 s) (levelProvider : Machine 256 l)
    (C R ci pi li prepFuel parentFuel : Nat) (ps ns : List PacketVector.Packet)
    (left right left0 right0 left' right' : PacketVector.Packet)
    (fields fields0 fields' : Fin 222→List Bool) (extra extra0 extra' : Fin 32→List Bool)
    (he : ns.length=ps.length) (hr : 1≤R) (hpi : pi+1≤R)
    (hp : ∀P∈ps,PacketVector.Fits R P) (hn : ∀P∈ns,PacketVector.Fits R P)
    (hprepare : Step (prepareLevel levelProvider) prepFuel (H (fun _=>0))
      (A C R ci pi li left right [] (PacketVector.bank R ps)
        (PacketVector.bank R (List.replicate ps.length [])) fields extra)
      (H (fun _=>0)) (A C R ci pi li left0 right0 [] (PacketVector.bank R ps)
        (PacketVector.bank R (List.replicate ps.length [])) fields0 extra0))
    (hparents : Step (parents provider) parentFuel (levelH (fun _=>0))
      (levelData C R ps.length ci 0 li left0 right0 (PacketVector.bank R ps)
        (PacketVector.bank R (List.replicate ps.length [])) fields0 extra0)
      (levelH (fun _=>0)) (levelData C R ps.length ps.length ps.length li left' right'
        (PacketVector.bank R ps) (PacketVector.bank R ns) fields' extra')) :
    Step (levelBody provider levelProvider)
      (prepFuel+parentFuel+VectorTransfer.budget R ps.length+2*R+9) (levelH (fun _=>0))
      (levelData C R ps.length ci pi li left right (PacketVector.bank R ps)
        (PacketVector.bank R (List.replicate ps.length [])) fields extra)
      (levelH (fun _=>0)) (levelData C R ps.length ps.length ps.length li left' right'
        (PacketVector.bank R ns) (PacketVector.bank R (List.replicate ps.length [])) fields' extra') := by
  have first:=hprepare.embed (fun _ : Fin 2=>1)
    (fun _ : Fin 2=>ZeroPadding.pad R (CompareMachine.word ps.length))
  have reset:=(reset_parent_run C R ps.length ci pi li left0 right0 [] (PacketVector.bank R ps)
    (PacketVector.bank R (List.replicate ps.length [])) (fun _=>0) fields0 extra0 hpi).embed
      (fun _ : Fin 1=>1) (fun _ : Fin 1=>ZeroPadding.pad R (CompareMachine.word ps.length))
  simp only [parentH,parentA,PhysicalAppendAssociativity.double] at reset
  have last:=transfer_run C R li ns ps left' right' (fun _=>0) fields' extra' he hr hn hp
  rw [he] at last
  have whole:=first.seq (reset.seq (hparents.seq last))
  have fuel : prepFuel+1+((2*R+6)+1+(parentFuel+1+VectorTransfer.budget R ps.length))=
      prepFuel+parentFuel+VectorTransfer.budget R ps.length+2*R+9 := by omega
  rw [fuel] at whole
  simpa only [levelBody,levelH,levelData,levelA] using whole

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp

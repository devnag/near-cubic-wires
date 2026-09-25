import Proof.Packets.PacketsXVectorWorkerData
import Proof.Packets.VectorControllerTransfer

/-! Actual turnover of the complete next vector into the previous vector in
the full298-port level arena, retaining all numeric workspace and drivers. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def levelH (mh : Fin 222→Nat) : Fin 298→Nat:=Fin.addCases (m:=296) (n:=2) (motive:=fun _=>Nat) (H mh) (fun _=>1)
def levelA (C R N li : Nat) (left right : PacketVector.Packet) (previous next : List Bool)
    (fields : Fin 222→List Bool) (extra : Fin 32→List Bool) : Fin 298→List Bool :=
  Fin.addCases (m:=296) (n:=2) (motive:=fun _=>List Bool)
    (A C R N N li left right [] previous next fields extra) (fun _=>ZeroPadding.pad R (CompareMachine.word N))

theorem banks_outside (C R ci pi li : Nat) (left right acc : PacketVector.Packet)
    (previous next previous' next' : List Bool) (fields : Fin 222→List Bool) (extra : Fin 32→List Bool)
    (i : Fin 296) (h0 : i≠256) (h1 : i≠257) :
    A C R ci pi li left right acc previous next fields extra i=
      A C R ci pi li left right acc previous' next' fields extra i := by
  revert h0 h1
  refine Fin.addCases (m:=264) (n:=32) (fun j=>?_) (fun j=>?_) i
  · intro h0 h1
    simp only [A,Fin.addCases_left]
    apply VectorController.banks_outside
    · intro he;subst j;exact h0 rfl
    · intro he;subst j;exact h1 rfl
  · intro _ _;simp only [A,Fin.addCases_right]

theorem transfer_tapes (C R N li : Nat) (left right : PacketVector.Packet) (previous next : List Bool)
    (fields : Fin 222→List Bool) (extra : Fin 32→List Bool) (i : Fin 6) :
    ZeroPadding.pad ((![0,0,0,0,R,R] : Fin 6→Nat) i) (VectorTransfer.tapes R N next previous i)=
      levelA C R N li left right previous next fields extra (transferSlots i) := by
  fin_cases i
  · exact ZeroPadding.pad_zero _
  · exact ZeroPadding.pad_zero _
  · exact ZeroPadding.pad_zero _
  · change ZeroPadding.pad 0 (List.replicate R false)=ZeroPadding.pad R []
    simp [ZeroPadding.pad]
  · change ZeroPadding.pad R []=List.replicate R false
    simp [ZeroPadding.pad]
  · rfl

attribute [local irreducible] VectorTransfer.machine transfer

theorem transfer_run (C R li : Nat) (ns ps : List PacketVector.Packet)
    (left right : PacketVector.Packet) (mh : Fin 222→Nat) (fields : Fin 222→List Bool) (extra : Fin 32→List Bool)
    (he : ns.length=ps.length) (hr : 1≤R)
    (hn : ∀P∈ns,PacketVector.Fits R P) (hp : ∀P∈ps,PacketVector.Fits R P) :
    Step transfer (VectorTransfer.budget R ns.length) (levelH mh)
      (levelA C R ns.length li left right (PacketVector.bank R ps) (PacketVector.bank R ns) fields extra)
      (levelH mh) (levelA C R ns.length li left right (PacketVector.bank R ns)
        (PacketVector.bank R (List.replicate ns.length [])) fields extra) := by
  have small:=(VectorBankTurnover.run R ns ps he hr hn hp).pad (![0,0,0,0,R,R] : Fin 6→Nat)
  unfold transfer
  apply PhysicalFocusBoundary.focus small transferSlots (by decide) (levelH mh) (levelH mh) _ _
  · intro i;fin_cases i <;>rfl
  · exact transfer_tapes C R ns.length li left right _ _ fields extra
  · intro i;fin_cases i <;>rfl
  · exact transfer_tapes C R ns.length li left right _ _ fields extra
  · intro i away
    refine ⟨rfl,?_⟩
    revert away
    refine Fin.addCases (m:=296) (n:=2) (fun j=>?_) (fun j=>?_) i
    · intro away
      simp only [levelA,Fin.addCases_left]
      apply banks_outside
      · intro he;subst j;exact away 2 rfl
      · intro he;subst j;exact away 1 rfl
    · intro _;simp only [levelA,Fin.addCases_right]

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp

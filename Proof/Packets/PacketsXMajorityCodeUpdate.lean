import Proof.Packets.PacketsXMajorityTermDefs
import Proof.Packets.PhysicalAppendUpdateRight

/-! Changing the enumerated assignment touches exactly one physical tape.
The arithmetic bank stays abstract during this frame proof. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityTermArena
open NormalizedFiniteTransport PairedPacketMeaning

theorem extras_binary_update (R N count : Nat) (bits out old new : List Bool) (flag : Bool) :
    Function.update (extras R N count bits out old flag) 7 new=
      extras R N count bits out new flag := by
  funext i
  fin_cases i <;>rfl

theorem binary_update (C R : Nat) (ps : List Poly) (left right : Poly)
    (bits : List Bool) (count : Nat) (flag : Bool) (out old new : List Bool) :
    Function.update (A C R ps left right bits count flag out old) 44 new=
      A C R ps left right bits count flag out new := by
  unfold A
  change Function.update
    (Fin.addCases (m:=37) (n:=9) (motive:=fun _=>List Bool)
      (OrderedPacketStep.A C R 0 left right (ComplementPacketBank.pairs ps))
      (extras R ps.length count bits out old flag)) ((7 : Fin 9).natAdd 37) new=_
  rw [PhysicalAppendUpdate.right,extras_binary_update]

theorem binary_other (C R : Nat) (ps : List Poly) (left right : Poly)
    (bits : List Bool) (count : Nat) (flag : Bool) (out old new : List Bool)
    (i : Fin 46) (hi : i≠44) :
    A C R ps left right bits count flag out old i=
      A C R ps left right bits count flag out new i := by
  have h:=congrFun (binary_update C R ps left right bits count flag out old new) i
  simpa only [Function.update_of_ne hi] using h

end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityTermArena

import Proof.Packets.PacketsXVectorWorkerProjection
import Proof.Packets.PhysicalAppendUpdateRight

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp

theorem update_meta (C R ci pi li : Nat) (left right acc : List (List Bool)) (previous next : List Bool)
    (fields : Fin 222→List Bool) (extra : Fin 32→List Bool) (i : Fin 222) (word : List Bool) :
    Function.update (A C R ci pi li left right acc previous next fields extra) ((i.natAdd 34).castAdd 40) word=
      A C R ci pi li left right acc previous next (Function.update fields i word) extra := by
  change Function.update (Fin.addCases (m:=264) (n:=32) (motive:=fun _=>List Bool) _ _)
    (((i.natAdd 34).castAdd 8).castAdd 32) word=_
  rw [PhysicalAppendUpdate.left]
  unfold VectorController.A
  rw [PhysicalAppendUpdate.left,PhysicalAppendUpdate.right]
  rfl

end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp

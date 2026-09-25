import Proof.Packets.PacketsXVectorWorkerData

/-! Small exact projection lemmas keep physical array proofs independent of
large machine definitions and reconstruct retained worker configurations. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

theorem A_core (C R ci pi li : Nat) (left right acc : List (List Bool)) (previous next : List Bool)
    (fields : Fin 222→List Bool) (extra : Fin 32→List Bool) (i : Fin 34) :
    A C R ci pi li left right acc previous next fields extra (i.castAdd 262)=ReusableArithmetic.state C R left right i := by
  change (Fin.addCases (m:=264) (n:=32) (motive:=fun _=>List Bool)
    (VectorController.A C R ci pi li left right acc previous next fields) extra) ((i.castAdd 230).castAdd 32)=_
  rw [Fin.addCases_left,VectorController.A_core]

theorem A_meta (C R ci pi li : Nat) (left right acc : List (List Bool)) (previous next : List Bool)
    (fields : Fin 222→List Bool) (extra : Fin 32→List Bool) (i : Fin 222) :
    A C R ci pi li left right acc previous next fields extra ((i.natAdd 34).castAdd 40)=fields i := by
  change (Fin.addCases (m:=264) (n:=32) (motive:=fun _=>List Bool)
    (VectorController.A C R ci pi li left right acc previous next fields) extra) (((i.natAdd 34).castAdd 8).castAdd 32)=_
  rw [Fin.addCases_left,VectorController.A_meta]

theorem A_saved (C R ci pi li : Nat) (left right acc : List (List Bool)) (previous next : List Bool)
    (fields : Fin 222→List Bool) (extra : Fin 32→List Bool) (i : Fin 8) :
    A C R ci pi li left right acc previous next fields extra ((i.natAdd 256).castAdd 32)=
      VectorController.extraTapes R ci pi li acc previous next i := by
  change (Fin.addCases (m:=264) (n:=32) (motive:=fun _=>List Bool)
    (VectorController.A C R ci pi li left right acc previous next fields) extra) ((i.natAdd 256).castAdd 32)=_
  rw [Fin.addCases_left,VectorController.A_extra]

theorem A_extra (C R ci pi li : Nat) (left right acc : List (List Bool)) (previous next : List Bool)
    (fields : Fin 222→List Bool) (extra : Fin 32→List Bool) (i : Fin 32) :
    A C R ci pi li left right acc previous next fields extra (i.natAdd 264)=extra i := Fin.addCases_right i

theorem reconstruct (C R ci pi li : Nat) (left right acc : List (List Bool)) (previous next : List Bool)
    (T : Fin 296→List Bool)
    (hcore : ∀i : Fin 34,T (i.castAdd 262)=ReusableArithmetic.state C R left right i)
    (hsaved : ∀i : Fin 8,T ((i.natAdd 256).castAdd 32)=VectorController.extraTapes R ci pi li acc previous next i) :
    T=A C R ci pi li left right acc previous next
      (fun i=>T ((i.natAdd 34).castAdd 40)) (fun i=>T (i.natAdd 264)) := by
  funext i
  refine Fin.addCases (m:=264) (n:=32) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=256) (n:=8) (fun k=>?_) (fun k=>?_) j
    · refine Fin.addCases (m:=34) (n:=222) (fun l=>?_) (fun l=>?_) k
      · rw [show ((l.castAdd 222).castAdd 8).castAdd 32=l.castAdd 262 from Fin.ext rfl,A_core]
        exact hcore l
      · rw [show ((l.natAdd 34).castAdd 8).castAdd 32=(l.natAdd 34).castAdd 40 from Fin.ext rfl,A_meta]
    · rw [A_saved];exact hsaved k
  · rw [A_extra]

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp

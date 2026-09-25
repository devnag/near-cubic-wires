import Proof.Packets.PacketsXVectorWorkerData

/-! Canonical counter updates and exact heads for the reusable vector arena. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

theorem heads_eq : H (fun _ : Fin 222=>0)=VectorWorkerArena.heads := by decide

theorem child_index (B R ci pi li : Nat) (left right acc : List (List Bool)) (previous next : List Bool)
    (fields : Fin 222→List Bool) (extra : Fin 32→List Bool) :
    A B R ci pi li left right acc previous next fields extra 258=ZeroPadding.pad R (CompareMachine.word ci) := rfl

theorem update_child_index (B R ci ci' pi li : Nat) (left right acc : List (List Bool)) (previous next : List Bool)
    (fields : Fin 222→List Bool) (extra : Fin 32→List Bool) :
    Function.update (A B R ci pi li left right acc previous next fields extra) 258
      (ZeroPadding.pad R (CompareMachine.word ci'))=
      A B R ci' pi li left right acc previous next fields extra := by
  funext i
  refine Fin.addCases (m:=264) (n:=32) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=256) (n:=8) (fun k=>?_) (fun k=>?_) j
    · have hn : (k.castAdd 8).castAdd 32≠(258 : Fin 296) := by
        intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega
      rw [Function.update_of_ne hn]
      simp only [A,VectorController.A,Fin.addCases_left]
    · fin_cases k <;>rfl
  · have hn : j.natAdd 264≠(258 : Fin 296) := by
      intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega
    rw [Function.update_of_ne hn]
    simp only [A,Fin.addCases_right]

theorem parent_index (B R ci pi li : Nat) (left right acc : List (List Bool)) (previous next : List Bool)
    (fields : Fin 222→List Bool) (extra : Fin 32→List Bool) :
    A B R ci pi li left right acc previous next fields extra 259=ZeroPadding.pad R (CompareMachine.word pi) := rfl

theorem update_parent_index (B R ci pi pi' li : Nat) (left right acc : List (List Bool)) (previous next : List Bool)
    (fields : Fin 222→List Bool) (extra : Fin 32→List Bool) :
    Function.update (A B R ci pi li left right acc previous next fields extra) 259
      (ZeroPadding.pad R (CompareMachine.word pi'))=
      A B R ci pi' li left right acc previous next fields extra := by
  funext i
  refine Fin.addCases (m:=264) (n:=32) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=256) (n:=8) (fun k=>?_) (fun k=>?_) j
    · have hn : (k.castAdd 8).castAdd 32≠(259 : Fin 296) := by
        intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega
      rw [Function.update_of_ne hn]
      simp only [A,VectorController.A,Fin.addCases_left]
    · fin_cases k <;>rfl
  · have hn : j.natAdd 264≠(259 : Fin 296) := by
      intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega
    rw [Function.update_of_ne hn]
    simp only [A,Fin.addCases_right]

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp

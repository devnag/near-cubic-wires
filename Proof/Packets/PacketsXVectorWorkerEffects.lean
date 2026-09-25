import Proof.Packets.PacketsXVectorWorkerProjection

/-! Exact canonical effects of the actual invalid-target zero branch and
numeric scratch erase. These align repeated metadata/provider calls. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

theorem A_right_outside (C R ci pi li : Nat) (left right right' acc : List (List Bool))
    (previous next : List Bool) (fields : Fin 222→List Bool) (extra : Fin 32→List Bool)
    (i : Fin 296) (h26 : i≠26) (h27 : i≠27) :
    A C R ci pi li left right acc previous next fields extra i=
      A C R ci pi li left right' acc previous next fields extra i := by
  revert h26 h27
  refine Fin.addCases (m:=264) (n:=32) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=256) (n:=8) (fun k=>?_) (fun k=>?_) j
    · refine Fin.addCases (m:=34) (n:=222) (fun l=>?_) (fun l=>?_) k
      · intro hn26 hn27
        rw [show ((l.castAdd 222).castAdd 8).castAdd 32=l.castAdd 262 from Fin.ext rfl,A_core,A_core]
        have h:=VectorAccumulator.tapes_right_outside C R left right right' [] (l.castAdd 2)
          (by intro he;apply hn26;apply Fin.ext;exact congrArg (fun z : Fin 36=>z.val) he)
          (by intro he;apply hn27;apply Fin.ext;exact congrArg (fun z : Fin 36=>z.val) he)
        simpa only [VectorAccumulator.tapes_engine] using h
      · intro _ _
        rw [show ((l.natAdd 34).castAdd 8).castAdd 32=(l.natAdd 34).castAdd 40 from Fin.ext rfl,A_meta,A_meta]
    · intro _ _;rw [A_saved,A_saved]
  · intro _ _;rw [A_extra,A_extra]

theorem right_zero_canonical (C R ci pi li : Nat) (left right acc : List (List Bool))
    (previous next : List Bool) (fields : Fin 222→List Bool) (extra : Fin 32→List Bool) (hr : 1≤R) :
    VectorWorkerArena.rightZero R (A C R ci pi li left right acc previous next fields extra)=
      A C R ci pi li left [] acc previous next fields extra := by
  funext i
  by_cases h26:i=26
  · subst i
    change List.replicate R false=ZeroPadding.pad R []
    simp [ZeroPadding.pad]
  by_cases h27:i=27
  · subst i
    exact (VectorAccumulator.zero_count R hr).symm
  simp only [VectorWorkerArena.rightZero,Function.update_of_ne h26,Function.update_of_ne h27]
  exact A_right_outside C R ci pi li left right [] acc previous next fields extra i h26 h27

def clearedExtra (R : Nat) (extra : Fin 32→List Bool) (i : Fin 32) : List Bool :=
  if i.val<17 then List.replicate R false else extra i

theorem cleared_canonical (C R ci pi li : Nat) (left right acc : List (List Bool))
    (previous next : List Bool) (fields : Fin 222→List Bool) (extra : Fin 32→List Bool) :
    VectorWorkerArena.cleared R (A C R ci pi li left right acc previous next fields extra)=
      A C R ci pi li left right acc previous next fields (clearedExtra R extra) := by
  funext i
  refine Fin.addCases (m:=264) (n:=32) (fun j=>?_) (fun j=>?_) i
  · have hn:¬(264≤(j.castAdd 32 : Fin 296).val ∧ (j.castAdd 32 : Fin 296).val<281) := by
      have hj:=j.isLt;simp only [Fin.val_castAdd];omega
    simp only [VectorWorkerArena.cleared,if_neg hn,A,Fin.addCases_left]
  · change (if 264≤264+j.val ∧ 264+j.val<281 then List.replicate R false
        else A C R ci pi li left right acc previous next fields extra (j.natAdd 264))=_
    rw [A_extra,A_extra]
    unfold clearedExtra
    by_cases hj:j.val<17
    · simp only [if_pos hj,if_pos (show 264≤264+j.val ∧ 264+j.val<281 by omega)]
    · simp only [if_neg hj,if_neg (show ¬(264≤264+j.val ∧ 264+j.val<281) by omega)]

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp

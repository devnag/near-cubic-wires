import Proof.CaseAnalysis.RowsModeCacheReuseRun

/-! The original ordinary mode-cache machine reuses the physically generated
common reserve. Its private-capacity driver is supplied by that actual reserve
producer; the machine never assumes a separately generated reuseCapacity. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ModeCacheCommon
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeCache
attribute [local irreducible] reuseMachine

def budget (p : Parameters) (M R : Nat) := 2*R+2*sourceBudget p M+7

theorem final_length (mode : Fin 3) (p : Parameters) (M R : Nat)
    (hD : reuseCapacity p M≤R) (i : Fin 15) : (reuseFinal mode p M R i).length=R := by
  unfold reuseFinal
  rw [ZeroPadding.pad_length,Nat.max_eq_left ((final_private_length mode p M [] i).trans hD)]

theorem run (mode : Fin 3) (p : Parameters) (M R : Nat) (out : List Bool) (A : Fin 15→List Bool)
    (hl : p.level≤p.rank) (hC : p.rank+2≤p.C)
    (hb : CloseoutRowsModeHashLoop.budget p.rank p.rank+2≤p.C)
    (hi : M≤2^p.rank) (hlog : sourceBudget p M≤R+3)
    (hD : reuseCapacity p M≤R) (hA : ∀i,(A i).length≤R) :
    Step (reuseMachine mode) (budget p M R)
      (reuseHeads out) (reuseData p M (R+3) R out A)
      (reuseHeads (out++sourceWord mode p M))
      (reuseData p M (R+3) R (out++sourceWord mode p M) (reuseFinal mode p M R)) := by
  have h:=(reuse_clear p M (R+3) R out A hA).seq
    (reuse_return mode p M (R+3) R out hl hC hb hi hlog
      (by unfold reuseCapacity at hD;omega) (by unfold reuseCapacity at hD;omega)
      (by unfold reuseCapacity at hD;omega))
  have hf : (2*R+4)+1+(2*sourceBudget p M+2)=budget p M R := by unfold budget;omega
  simpa only [reuseMachine,hf] using h

noncomputable def delta := Composition.machine (reuseMachine 1) (reuseMachine 2)
attribute [local irreducible] delta

theorem delta_run (p : Parameters) (M R : Nat) (out : List Bool) (A : Fin 15→List Bool)
    (hl : p.level≤p.rank) (hC : p.rank+2≤p.C)
    (hb : CloseoutRowsModeHashLoop.budget p.rank p.rank+2≤p.C)
    (hi : M≤2^p.rank) (hlog : sourceBudget p M≤R+3)
    (hD : reuseCapacity p M≤R) (hA : ∀i,(A i).length≤R) :
    Step delta (2*budget p M R+1)
      (reuseHeads out) (reuseData p M (R+3) R out A)
      (reuseHeads (out++CloseoutRowsRawPairSeek.cacheWord (pairs 1 p M++pairs 2 p M)))
      (reuseData p M (R+3) R (out++CloseoutRowsRawPairSeek.cacheWord (pairs 1 p M++pairs 2 p M))
        (reuseFinal 2 p M R)) := by
  have h:=(run 1 p M R out A hl hC hb hi hlog hD hA).seq
    (run 2 p M R _ _ hl hC hb hi hlog hD (fun i=>(final_length 1 p M R hD i).le))
  have he : (out++sourceWord 1 p M)++sourceWord 2 p M=
      out++CloseoutRowsRawPairSeek.cacheWord (pairs 1 p M++pairs 2 p M) := by
    simp only [source_word,CloseoutRowsRawPairSeek.cacheWord,List.flatMap_append,List.append_assoc]
  rw [he] at h
  have hf : budget p M R+1+budget p M R=2*budget p M R+1 := by omega
  simpa only [delta,hf] using h

end PCJ9eff70d512234a4c_Fixed.Materializer.ModeCacheCommon

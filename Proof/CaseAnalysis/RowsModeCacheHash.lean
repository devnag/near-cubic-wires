import Proof.CaseAnalysis.RowsModeCacheLayout

/-! The cache body computes the original seed hash and actual cell flags.
Only the fixed hash work bank and three singleton flags are touched. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def hashMachine:=TapeEmbedding.machine 13 CloseoutRowsModeHashReady.machine
noncomputable def guardMachine:=RecoveryFocus.machine guardSlots CloseoutRowsModeHashGuard.machine

theorem hash_run (p : Parameters) (s : State) (hC : p.rank+2≤p.C)
    (hb : CloseoutRowsModeHashLoop.budget p.rank p.rank+2≤p.C) :
    Step hashMachine (CloseoutRowsModeHashReady.budget p.rank p.rank)
      (heads s) (data p s false) (heads s) (data p s true):=by
  have r:=CloseoutRowsModeHashReady.ready p.rank p.rank p.C (label p s) p.lower p.upper p.translation (by omega) hC hb
  rw [CloseoutRowsModeHashFields.input_eq _ _ _ _ _ _ _ (by omega),CloseoutRowsModeHashFields.output_eq] at r
  exact r.embed (extraHeads s 0) (extras p s)

theorem guard_run (p : Parameters) (s : State) (hl : p.level≤p.rank) (hC : p.rank+2≤p.C) :
    Step guardMachine (2*p.level+6) (heads s) (data p s true)
      (heads (guarded p s)) (data p (guarded p s) true):=by
  have hi:Function.Injective guardSlots:=by decide
  have hlen:(hashWord p s).length=p.rank:=CloseoutRowsModeHashFields.word_length _ _ _ _ _ _
  have ht:((hashWord p s).take p.level).length=p.level:=by simp [hlen,Nat.min_eq_left hl]
  have hword:(hashWord p s).take p.level++((hashWord p s).drop p.level++List.replicate (p.C-p.rank) false)=
      ZeroPadding.pad p.C (hashWord p s):=by
    rw [←List.append_assoc,List.take_append_drop]
    simp only [ZeroPadding.pad,hlen]
  have r:=CloseoutRowsModeHashGuard.ready ((hashWord p s).take p.level)
    ((hashWord p s).drop p.level++List.replicate (p.C-p.rank) false) p.C s.zero s.sibling s.child (by omega)
  rw [ht,hword,ZeroPadding.read_pad] at r
  have d:=r.dock guardSlots hi (heads s) (data p s true)
    (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> rfl)
  apply d.congr
  · exact dockH_existing guardSlots (heads s) (fun _=>0) (by intro i;fin_cases i <;> rfl)
  · apply HierarchyAllocation.install_eq guardSlots hi
    · intro i;fin_cases i <;> rfl
    · intro i h
      fin_cases i
      all_goals first | rfl | exact False.elim (h 0 rfl) | exact False.elim (h 1 rfl) |
        exact False.elim (h 2 rfl) | exact False.elim (h 3 rfl) | exact False.elim (h 4 rfl)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache

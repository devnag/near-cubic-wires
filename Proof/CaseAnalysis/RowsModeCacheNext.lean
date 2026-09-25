import Proof.CaseAnalysis.RowsModeCachePair

/-! The real binary label advances, then just the three private hash fields
are cleared from the paid original capacity. The next population body reuses
all original seed, mask, level, index and count fields. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def labelMachine:=RecoveryFocus.machine labelSlots (Rewind.machine BinaryIncrement.machine)
noncomputable def eraseMachine:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 3)
def labelData (p : Parameters) (s : State) : Fin 24→List Bool:=
  Function.update (pairData p s) 1 (label p (emitted s))

theorem label_run (p : Parameters) (s : State) (hi : s.index<2^p.rank) (hC : p.rank+1≤p.C) :
    Step labelMachine (2*p.rank+4) (heads (emitted s)) (pairData p s)
      (heads (emitted s)) (labelData p s):=by
  have hs:Function.Injective labelSlots:=by decide
  have r:=CloseoutRowsModeLabel.advance p.rank s.index p.C hi hC
  have d:=r.dock labelSlots hs (heads (emitted s)) (pairData p s)
    (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> rfl)
  apply d.congr
  · exact dockH_existing labelSlots _ _ (by intro i;fin_cases i <;> rfl)
  · apply HierarchyAllocation.install_eq labelSlots hs
    · intro i;fin_cases i <;> rfl
    · intro i h
      simp only [labelData,Function.update_of_ne (show i≠1 by intro he;exact h 0 he.symm)]

theorem erased_data (p : Parameters) (s : State) :
    data p (emitted s) false=
      Function.update (Function.update (Function.update (labelData p s) 4 (List.replicate p.C false))
        6 (List.replicate p.C false)) 8 (List.replicate p.C false):=by
  funext i;fin_cases i <;> rfl

theorem erase_run (p : Parameters) (s : State) (hC : p.rank+2≤p.C) :
    Step eraseMachine (2*p.C+4) (heads (emitted s)) (labelData p s)
      (heads (emitted s)) (data p (emitted s) false):=by
  have hi:Function.Injective eraseSlots:=by decide
  let backing : Fin 3→List Bool:=![labelData p s 4,labelData p s 6,labelData p s 8]
  have hlen:(hashWord p s).length=p.rank:=CloseoutRowsModeHashFields.word_length _ _ _ _ _ _
  unfold hashWord at hlen
  have hb:∀ i,(backing i).length≤p.C:=by
    intro i;fin_cases i <;>
      simp [backing,labelData,pairData,fields,CloseoutRowsModeHashFields.after,Fin.addCases,
        ZeroPadding.pad_length,CompareMachine.word,hlen] <;> omega
  have r:=Step.of_ready (RecoveryScratchErase.erase_ready p.C (p.C+1) backing hb)
  simp only [max_self] at r
  have d:=r.dock eraseSlots hi (heads (emitted s)) (labelData p s)
    (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> rfl)
  apply d.congr
  · exact dockH_existing eraseSlots _ _ (by intro i;fin_cases i <;> rfl)
  · apply HierarchyAllocation.install_eq eraseSlots hi
    · intro i;fin_cases i <;> rfl
    · intro i h
      have h4:i≠4:=by intro he;exact h 0 he.symm
      have h6:i≠6:=by intro he;exact h 1 he.symm
      have h8:i≠8:=by intro he;exact h 2 he.symm
      rw [erased_data]
      simp only [Function.update_of_ne h4,Function.update_of_ne h6,Function.update_of_ne h8]

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache

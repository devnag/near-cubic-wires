import Proof.CaseAnalysis.RowsModeElementaryBoundary

/-! The actual cold elementary run is recorded, returned, and physically
cleared. Only the appended raw monomials survive in its work bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryReuse
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CloseoutRowsModeElementaryLayout
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first : Σ s,Machine 52 s:=
  ⟨_,TapeEmbedding.machine 6 (CloseoutRowsModeElementaryReset.machine CloseoutRowsModeElementary.machine)⟩
noncomputable def machine:=Composition.machine first.2 CloseoutRowsModeElementaryClear.machine
def budget (w k M C : Nat):=CloseoutRowsModeElementaryReset.budget (CloseoutRowsModeElementary.budget w k M)+1+(2*C+4)

theorem body_run (w k M C : Nat) (out : List Bool) (hM : 0<M) (hMw : M≤2^w)
    (hmeta : 2*w+k+3≤C) (hC : CloseoutRowsModeElementary.budget w k M+1≤C) :
    ∃ r,runFrom machine (budget w k M C)
      ⟨machine.start,heads out,(loaded w k M C out).tapes⟩=some r ∧
      r.final.heads=heads (out++CloseoutRowsModeElementary.bodyWord w k M) ∧
      r.final.tapes=blank w k M C (out++CloseoutRowsModeElementary.bodyWord w k M) ∧
      r.steps≤budget w k M C:=by
  obtain ⟨a,ha,a44,ah44,_,_,_,_,_⟩:=CloseoutRowsModeElementary.elementary_run w k M out hM hMw
  have initial_heads:∀ i,CloseoutRowsModeElementaryReset.selected i=true → (raw w k M out).heads i=0:=by
    intro i hi;fin_cases i
    all_goals first | rfl | (simp [CloseoutRowsModeElementaryReset.selected] at hi)
  have initial_tapes:∀ i,CloseoutRowsModeElementaryReset.selected i=true → ((raw w k M out).tapes i).length≤C:=by
    intro i hi;fin_cases i
    all_goals first
      | (simp [CloseoutRowsModeElementaryReset.selected] at hi;done)
      | (simp [raw,CloseoutRowsModeElementary.input,CloseoutRowsModeElementary.extraTapes,
          RowTupleEnumerationReady.input,RowTupleDerivedEnumeration.input,Fin.addCases,
          CompareMachine.word,frame_length,SignedSortKey.binary_length] <;> omega)
  obtain ⟨r,hr,rh,rt,rh45,rt45,rl,_⟩:=CloseoutRowsModeElementaryReset.reset_run
    CloseoutRowsModeElementary.machine (raw w k M out) _ C a ha initial_heads initial_tapes hC
  let c:=TapeEmbedding.receipt (fun _ : Fin 6=>0) (extra w k M C) r
  have hc:=TapeEmbedding.run_embed (CloseoutRowsModeElementaryReset.machine CloseoutRowsModeElementary.machine)
    (fun _ : Fin 6=>0) (extra w k M C) _ _ r hr
  have initial:loaded w k M C out=
      (⟨first.2.start,heads out,(loaded w k M C out).tapes⟩ : Configuration 52 first.1):=by
    apply configuration_ext
    · rfl
    · exact loaded_heads w k M C out
    · rfl
  change runFrom first.2 _ (loaded w k M C out)=some c at hc
  rw [initial] at hc
  have ch:c.final.heads=heads (out++CloseoutRowsModeElementary.bodyWord w k M):=by
    have old (i : Fin 45):c.final.heads (i.castAdd 7)=
        if CloseoutRowsModeElementaryReset.selected i then 0 else a.final.heads i:=by
      change c.final.heads ((i.castAdd 1).castAdd 6)=_
      simpa only [c,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left] using rh i
    funext i
    refine Fin.addCases (m:=45) (n:=7) (fun j=>?_) (fun j=>?_) i
    · rw [old]
      by_cases hj:j=44
      · subst j;exact ah44
      · have hn:(j.castAdd 7 : Fin 52)≠44:=by simpa [Fin.ext_iff] using hj
        simp [CloseoutRowsModeElementaryReset.selected,hj,heads,hn]
    · fin_cases j <;> first | exact rh45 | rfl
  have c44:c.final.tapes 44=out++CloseoutRowsModeElementary.bodyWord w k M:=by
    have h:=rt 44
    change c.final.tapes 44=ZeroPadding.pad 0 (a.final.tapes 44) at h
    exact h.trans ((ZeroPadding.pad_zero _).trans a44)
  have hfit:∀ j,(c.final.tapes (CloseoutRowsModeElementaryClear.saved j)).length≤C:=by
    have len (i : Fin 45) (hi : CloseoutRowsModeElementaryReset.selected i=true):
        (c.final.tapes (i.castAdd 7)).length=C:=by
      change (c.final.tapes ((i.castAdd 1).castAdd 6)).length=C
      simpa only [c,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left] using rl i hi
    intro j
    by_cases hj:j.val<44
    · have he:CloseoutRowsModeElementaryClear.saved j=j.castAdd 7:=by
        simp only [CloseoutRowsModeElementaryClear.saved,hj,dif_pos];rfl
      rw [he]
      exact (len j (by simp [CloseoutRowsModeElementaryReset.selected,Fin.ext_iff];omega)).le
    · have he:j=44:=Fin.ext (by omega)
      subst j
      change (r.final.tapes 45).length≤C
      rw [rt45];simp
  obtain ⟨z,hz,_,zh,zt⟩:=CloseoutRowsModeElementaryClear.clear_run c.final.heads c.final.tapes C
    (by intro i;rw [ch];fin_cases i <;> rfl) (by rfl) (by rfl) hfit
  have whole:=Composition.run_join first.2 CloseoutRowsModeElementaryClear.machine _ _ _ c z hc hz
  have boundary:CloseoutRowsModeElementaryClear.output c.final.tapes C=
      flatBlank w k M C (out++CloseoutRowsModeElementary.bodyWord w k M):=by
    funext i;fin_cases i
    all_goals first | rfl | exact c44
  exact ⟨Composition.joinedReceipt c z,whole,zh.trans ch,
    zt.trans (boundary.trans (blank_eq _ _ _ _ _).symm),runFrom_steps_le machine _ _ _ whole⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryReuse

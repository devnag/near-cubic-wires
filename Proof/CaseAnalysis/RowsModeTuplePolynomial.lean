import Proof.CaseAnalysis.RowsModeTupleMonomial

/-! The actual selected-tuple frames drive the whole raw polynomial writer.
No count prepass or exponential unary driver is supplied to this loop. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeTuplePolynomial
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open CloseoutRowsModeTupleMonomial
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def idle : Machine 7 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
noncomputable def body : Σ s,Machine 7 s:=⟨_,CloseoutRowsModeTupleMonomial.machine⟩
noncomputable def sizes : Fin 2→Nat:=![1,body.1]
noncomputable def programs : (i : Fin 2)→Machine 7 (sizes i)
  | ⟨0,_⟩=>idle
  | ⟨1,_⟩=>body.2
  | ⟨n+2,h⟩=>False.elim (by omega)
def next (i : Fin 2) (_ : Fin (sizes i)) (bits : Fin 7→Bool) : Option (Fin 2):=
  if i=0 then if bits 0 then some 1 else none else some 0
noncomputable def machine:=RecoveryCalls.machine sizes programs 0 next
noncomputable def entry (i : Fin 2) (w k C pos : Nat) (source copy out : List Bool):=
  controlConfig (RecoveryCalls.code sizes i)
    (⟨(programs i).start,heads pos out,data w k C source copy out⟩ : Configuration 7 (sizes i))
noncomputable def final (w k C pos : Nat) (source copy out : List Bool):=
  RecoveryCalls.stopped sizes (heads pos out) (data w k C source copy out)
def sourceWord (w : Nat) (ps : List (List Nat)):=ps.flatMap (RowTupleFramedBody.word w)
def budget (w k M count : Nat):=count*(CloseoutRowsModeTupleMonomial.budget w k M+2)+1

theorem probe (w k C : Nat) (pre tail copy out : List Bool) :
    Timed machine 1 (entry 0 w k C pre.length (pre++true::tail) copy out)
      (entry 1 w k C pre.length (pre++true::tail) copy out) := by
  have hn:next 0 (programs 0).start
      (⟨(programs 0).start,heads pre.length out,data w k C (pre++true::tail) copy out⟩ :
        Configuration 7 (sizes 0)).scanned=some 1:=by
    simp [next,Configuration.scanned,heads,data,Streaming.read_append]
  exact Timed.single (by simp [machine,entry,RecoveryCalls.machine,controlConfig,RecoveryCalls.code])
    (RecoveryCalls.return_step sizes programs 0 next 0 1 _ (by rfl) hn)

theorem stop (w k C : Nat) (pre copy out : List Bool) :
    Timed machine 1 (entry 0 w k C pre.length pre copy out)
      (final w k C pre.length pre copy out) := by
  have hn:next 0 (programs 0).start
      (⟨(programs 0).start,heads pre.length out,data w k C pre copy out⟩ :
        Configuration 7 (sizes 0)).scanned=none:=by
    simp [next,Configuration.scanned,heads,data,readTapeBit,List.getD]
  exact Timed.single (by simp [machine,entry,RecoveryCalls.machine,controlConfig,RecoveryCalls.code])
    (RecoveryCalls.stop_step sizes programs 0 next 0 _ (by rfl) hn)

theorem round (w C M : Nat) (ds : List Nat) (pre tail copy out : List Bool)
    (hc : 2*w+1≤C) (hcopy : copy.length≤w) (hd : ∀ d∈ds,d<2^w) (hM : ∀ d∈ds,d≤M) :
    ∃ residue,residue.length≤w ∧ ∃ time≤CloseoutRowsModeTupleMonomial.budget w ds.length M+1,
      Timed machine time (entry 1 w ds.length C pre.length (pre++RowTupleFramedBody.word w ds++tail) copy out)
        (entry 0 w ds.length C (pre.length+(RowTupleFramedBody.word w ds).length)
          (pre++RowTupleFramedBody.word w ds++tail) residue (out++ExtIncidence.monomialWord ds)) := by
  obtain ⟨residue,hres,r,hr,rh,rt,_⟩:=monomial_run w C M ds pre tail copy out hc hcopy hd hM
  obtain ⟨time,ht,tr⟩:=call_receipt sizes programs 0 next 1 0 _ _ r hr (by rfl)
  have same:RecoveryCalls.restarted (programs 0) r.final.heads r.final.tapes=
      (⟨(programs 0).start,heads (pre.length+(RowTupleFramedBody.word w ds).length) (out++ExtIncidence.monomialWord ds),
        data w ds.length C (pre++RowTupleFramedBody.word w ds++tail) residue (out++ExtIncidence.monomialWord ds)⟩ :
        Configuration 7 (sizes 0)):=by
    apply configuration_ext
    · rfl
    · exact rh
    · exact rt
  rw [same] at tr
  exact ⟨residue,hres,time,ht,tr⟩

theorem remaining (w k C M : Nat) (ps : List (List Nat)) (pre copy out : List Bool)
    (hc : 2*w+1≤C) (hcopy : copy.length≤w) (hk : ∀ ds∈ps,ds.length=k)
    (hd : ∀ ds∈ps,∀ d∈ds,d<2^w) (hM : ∀ ds∈ps,∀ d∈ds,d≤M) :
    ∃ residue,residue.length≤w ∧ ∃ time≤budget w k M ps.length,
      Timed machine time (entry 0 w k C pre.length (pre++sourceWord w ps) copy out)
        (final w k C (pre.length+(sourceWord w ps).length) (pre++sourceWord w ps) residue
          (out++ps.flatMap ExtIncidence.monomialWord)) := by
  induction ps generalizing pre copy out with
  | nil =>
      refine ⟨copy,hcopy,1,by simp [budget],?_⟩
      simpa [sourceWord] using stop w k C pre copy out
  | cons ds ps ih =>
      have hlen:=hk ds (by simp)
      obtain ⟨nextCopy,hl,time,ht,tr⟩:=round w C M ds pre (sourceWord w ps) copy out hc hcopy
        (hd ds (by simp)) (hM ds (by simp))
      rw [hlen] at tr ht
      obtain ⟨residue,hres,restTime,hrest,rest⟩:=ih (pre++RowTupleFramedBody.word w ds) nextCopy
        (out++ExtIncidence.monomialWord ds) hl (fun x hx=>hk x (by simp [hx]))
        (fun x hx=>hd x (by simp [hx])) (fun x hx=>hM x (by simp [hx]))
      have first:=probe w k C pre
        ((SignedSortKey.binary (w*ds.length+1) (RowTupleDigits.encode w ds)).head! ::
          frame ((SignedSortKey.binary (w*ds.length+1) (RowTupleDigits.encode w ds)).tail)++sourceWord w ps) copy out
      have source : pre++true::
          ((SignedSortKey.binary (w*ds.length+1) (RowTupleDigits.encode w ds)).head! ::
            frame ((SignedSortKey.binary (w*ds.length+1) (RowTupleDigits.encode w ds)).tail)++sourceWord w ps)=
          pre++RowTupleFramedBody.word w ds++sourceWord w ps:=by
        simp [RowTupleFramedBody.word,SignedSortKey.binary,frame,RepairOrdinary.frame,List.append_assoc]
      rw [source] at first
      simp only [List.length_append,List.append_assoc] at rest tr first
      have whole:=first.trans (tr.trans rest)
      refine ⟨residue,hres,1+(time+restTime),?_,?_⟩
      · unfold budget at *;simp only [List.length_cons];nlinarith
      · simpa only [sourceWord,List.flatMap_cons,List.length_append,List.append_assoc,Nat.add_assoc] using whole

end NearCubicWires.RepairOrdinary.CloseoutRowsModeTuplePolynomial

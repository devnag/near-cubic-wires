import Proof.MachineModel.OrdinaryMatrixBatchGatePrepare

/-! One complete repeated raw gate body: physical work clear, zero copies,
cut extraction, all2U scoring, sort/rank and packet append with local returns. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchGateBody
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch
open MatrixScoreReusableRanks (D)
open MatrixBatchGateClear (tapes heads)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def native (i : Fin 43) : Fin 48 := i.castAdd 5
theorem native_injective : Function.Injective native := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 48 => a.val) h)
theorem native_fresh (i : Fin 5) : RecoveryFocus.pick native (i.natAdd 43)=none := by
  fin_cases i <;> decide
theorem heads_old (pos outlen : ℕ) (i : Fin 41) :
    heads pos outlen (i.castAdd 7)=MatrixScoreRetainedRanks.retainedHeads i := by
  fin_cases i <;> rfl
theorem ranked_tapes (r : Request) (gate : Fin r.Gates) (out : List Bool) :
    (MatrixBatchRankedGate.input r gate out).tapes=
      Fin.addCases (m := 41) (n := 2) (motive := fun _ => List Bool)
        (fun i => ZeroPadding.pad (MatrixScoreReusableRanks.capacities r i) (MatrixScoreReusableRanks.fields r gate i))
        ![out,List.replicate (D r) false] := by
  change (Fin.addCases (m := 41) (n := 2) (motive := fun _ => List Bool)
    (fun i => ZeroPadding.pad (MatrixScoreReusableRanks.capacities r i)
      ((MatrixScoreRetainedRanks.input r gate (MatrixScoreReusableRanks.cold r)).tapes i))
    ![out,List.replicate (D r) false])=_
  rw [MatrixScoreReusableRanks.input_fields]
theorem ranked_heads (r : Request) (gate : Fin r.Gates) (out : List Bool) :
    (MatrixBatchRankedGate.input r gate out).heads=
      Fin.addCases (m := 41) (n := 2) (motive := fun _ => ℕ)
        MatrixScoreRetainedRanks.retainedHeads ![out.length,0] := by
  change (Fin.addCases (m := 41) (n := 2) (motive := fun _ => ℕ)
    (MatrixScoreRetainedRanks.input r gate (MatrixScoreReusableRanks.cold r)).heads ![out.length,0])=_
  rw [MatrixScoreReusableRanks.input_heads]
theorem input_tapes (r : Request) (gate : Fin r.Gates) (cap : ℕ) (source out : List Bool) (i : Fin 43) :
    tapes r 0 0 cap source out (MatrixBatchGateBank.loaded r gate) (native i)=
      (MatrixBatchRankedGate.input r gate out).tapes i := by
  rw [ranked_tapes]
  fin_cases i <;> simp [native,tapes,install,MatrixBatchGateClear.pick_scratch,MatrixBatchGateClear.scratchPick,
    MatrixBatchGateClear.stable,MatrixBatchGateBank.loaded,Fin.addCases,MatrixScoreReusableRanks.fields,
    MatrixScoreReusableRanks.capacities,MatrixScoreReusableRanks.fixed,ZeroPadding.pad,MatrixScoreWeight.zeros]
theorem input_heads (r : Request) (gate : Fin r.Gates) (pos : ℕ) (out : List Bool) (i : Fin 43) :
    heads pos out.length (native i)=(MatrixBatchRankedGate.input r gate out).heads i := by
  rw [ranked_heads]
  fin_cases i <;> rfl

noncomputable def call := RecoveryFocus.machine native MatrixBatchRankedGate.machine
noncomputable def machine := Composition.machine MatrixBatchGatePrepare.machine call
noncomputable def budget (r : Request) (gate : Fin r.Gates) :=
  MatrixBatchGatePrepare.budget r+1+MatrixBatchRankedGate.budget r gate
noncomputable def input (r : Request) (gate : Fin r.Gates) (assignment id cap : ℕ)
    (pre suffix out : List Bool) (backing : Fin 31 → List Bool) :=
  RecoveryCalls.restarted machine (heads pre.length out.length)
    (tapes r assignment id cap (pre++cutWord r.p (r.cuts.get gate)++suffix) out backing)

theorem body_run (r : Request) (gate : Fin r.Gates) (assignment id cap : ℕ)
    (pre suffix out : List Bool) (backing : Fin 31 → List Bool) (hb : ∀ i,(backing i).length≤D r) :
    ∃ final : MatrixScoreLeftLoop.State r,∃ actual,
      runFrom machine (budget r gate) (input r gate assignment id cap pre suffix out backing)=some actual ∧
      actual.final.heads=heads (pre.length+(cutWord r.p (r.cuts.get gate)).length)
        (out++MatrixScoreRawRanks.output r gate).length ∧
      actual.final.tapes 41=out++MatrixScoreRawRanks.output r gate ∧
      actual.final.tapes 42=List.replicate (D r) false ∧
      actual.final.tapes 43=frame (SignedSortKey.binary r.M 0) ∧
      actual.final.tapes 44=List.replicate (D r) true ∧
      actual.final.tapes 45=List.replicate (max cap (D r+1)) false ∧
      actual.final.tapes 46=pre++cutWord r.p (r.cuts.get gate)++suffix ∧
      actual.final.tapes 47=List.replicate (D r) false ∧
      (∀ i : Fin 29,i≠24 → actual.final.tapes (i.castAdd 19)=
        ZeroPadding.pad (MatrixScoreReusableRanks.capacities r (i.castAdd 12))
          (MatrixScoreRetainedRanks.finalFields r gate final i)) ∧
      (∀ i : Fin 41,(actual.final.tapes (i.castAdd 7)).length≤D r) ∧
      actual.steps≤budget r gate := by
  obtain ⟨prepared,hp,ph,pt,ps⟩ := MatrixBatchGatePrepare.prepare_run r gate assignment id cap pre suffix out backing hb
  obtain ⟨final,body,hr,b41,h41,b42,h42,bt,bh,bfit,bs⟩ := MatrixBatchRankedGate.gate_run r gate out
  have hi : RecoveryFocus.config native prepared.final.heads prepared.final.tapes (MatrixBatchRankedGate.input r gate out)=
      Composition.restart prepared.final call.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [ph]
      exact input_heads r gate _ out i
    · intro i
      rw [pt]
      exact input_tapes r gate _ _ out i
  obtain ⟨focused,hf,hff,hfs⟩ := RecoveryFocus.run_config native native_injective MatrixBatchRankedGate.machine
    prepared.final.heads prepared.final.tapes _ _ body hr
  rw [hi] at hf
  have joined := Composition.run_join MatrixBatchGatePrepare.machine call _ _ _ prepared focused hp hf
  have localT (i : Fin 43) : focused.final.tapes (native i)=body.final.tapes i := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot native native_injective]
  have localH (i : Fin 43) : focused.final.heads (native i)=body.final.heads i := by
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot native native_injective]
  have freshT (i : Fin 5) : focused.final.tapes (i.natAdd 43)=prepared.final.tapes (i.natAdd 43) := by
    rw [hff]
    simp only [RecoveryFocus.config,native_fresh]
  have freshH (i : Fin 5) : focused.final.heads (i.natAdd 43)=prepared.final.heads (i.natAdd 43) := by
    rw [hff]
    simp only [RecoveryFocus.config,native_fresh]
  have constants : focused.final.tapes 43=frame (SignedSortKey.binary r.M 0) ∧
      focused.final.tapes 44=List.replicate (D r) true ∧
      focused.final.tapes 45=List.replicate (max cap (D r+1)) false ∧
      focused.final.tapes 46=pre++cutWord r.p (r.cuts.get gate)++suffix ∧
      focused.final.tapes 47=List.replicate (D r) false := by
    have hf0 := (freshT 0).trans (congrFun pt 43)
    have hf1 := (freshT 1).trans (congrFun pt 44)
    have hf2 := (freshT 2).trans (congrFun pt 45)
    have hf3 := (freshT 3).trans (congrFun pt 46)
    have hf4 := (freshT 4).trans (congrFun pt 47)
    simpa [tapes,install,MatrixBatchGateClear.pick_scratch,MatrixBatchGateClear.scratchPick,
      MatrixBatchGateClear.stable,MatrixBatchGateBank.loaded] using And.intro hf0 (And.intro hf1 (And.intro hf2 (And.intro hf3 hf4)))
  refine ⟨final,Composition.joinedReceipt prepared focused,joined,?_,(localT 41).trans b41,(localT 42).trans b42,
    constants.1,constants.2.1,constants.2.2.1,constants.2.2.2.1,constants.2.2.2.2,?_,?_,?_⟩
  · change focused.final.heads=_
    funext i
    refine Fin.addCases (m := 41) (n := 7) (motive := fun j => focused.final.heads j=_ ) ?_ ?_ i
    · intro j
      have hl := (localH (j.castAdd 2)).trans (bh j)
      exact hl.trans (heads_old _ _ j).symm
    · intro j
      fin_cases j
      · exact (localH 41).trans h41
      · exact (localH 42).trans h42
      · exact (freshH 0).trans (congrFun ph 43)
      · exact (freshH 1).trans (congrFun ph 44)
      · exact (freshH 2).trans (congrFun ph 45)
      · exact (freshH 3).trans (congrFun ph 46)
      · exact (freshH 4).trans (congrFun ph 47)
  · intro i hn
    exact (localT (i.castAdd 14)).trans (bt i hn)
  · intro i
    have ht := localT (i.castAdd 2)
    exact (congrArg List.length ht).trans_le (bfit i)
  · change prepared.steps+1+focused.steps≤_
    rw [hfs]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixBatchGateBody

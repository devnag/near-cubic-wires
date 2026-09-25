import Proof.MachineModel.TopDownPaidFamilySum

/-! The actual reusable family machine, complete source invariant, and
physical raw rewind/sum in a single fixed program. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9856d3e73b1d4df0_.FamilySum
open NearCubicWires LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open RecoveryRootRound RecoveryExecution SignedSortKey
open RepairSource.CloseoutFinal.C10ExternalRowLoop CloseoutFinalC10RowAnswerWord
open P1TopDownPaidReusable (Datum Valid source outputSlot)
open RepairSource.VerifierDecoding
attribute [local irreducible] P1TopDownPaidReusable.machine CompetitorCrossScheduler.producer

noncomputable def raw (a : WilliamsAlgorithm) := (outputSlot a).castAdd 1
noncomputable def entry (a : WilliamsAlgorithm) (ds : List Datum) (S R B N : Nat) :=
  RepeatMachine.cfg 0 (source a ds S R B 0 []) N 1
noncomputable def after (a : WilliamsAlgorithm) (ds : List Datum) (S R B b : Nat) (xs : List Nat) :=
  RepeatMachine.cfg 3 (source a ds S R B xs.length (CompetitorCountFold.raw b xs)) xs.length 1
noncomputable def machine (a : WilliamsAlgorithm) :=
  Composition.machine (TapeEmbedding.machine 11 (familyWriter (P1TopDownPaidReusable.machine a)))
    (P1TopDownPaidFamilySum.machine (raw a))
noncomputable def budget (a : WilliamsAlgorithm) (S b v N : Nat) :=
  familyFuel N ((3*P1TopDownPaidPayload.tapes a+6)*(S+1))+1+P1TopDownPaidFamilySum.budget b v N

set_option maxHeartbeats 1000000 in
theorem family_run (a : WilliamsAlgorithm) (ds : List Datum) (dflt : Datum) (S R B b : Nat) (xs : List Nat)
    (hv : ∀ k (hk : k<ds.length),Valid a B R S ds[k])
    (hwords : ds.map Datum.emit=xs.map (binary b)) :
    Step (familyWriter (P1TopDownPaidReusable.machine a))
      (familyFuel xs.length ((3*P1TopDownPaidPayload.tapes a+6)*(S+1)))
      (entry a ds S R B xs.length).heads (entry a ds S R B xs.length).tapes
      (after a ds S R B b xs).heads (after a ds S R B b xs).tapes := by
  obtain ⟨rc,hr,hf,ht⟩:=CloseoutRowsDegreeLoop.loop_run (P1TopDownPaidReusable.machine a)
    (source a ds S R B) (fun k=>(xs.map (binary b)).getD k [])
    ((3*P1TopDownPaidPayload.tapes a+6)*(S+1)) (xs.map (binary b)).length
    (by intros;rfl)
    (P1TopDownPaidReusable.hrow_words a ds dflt S R B _ _ hv
      (fun k hk=>P1TopDownPaidReusable.uniform_budget a B R S _ (hv k hk)) hwords) []
  rw [flatten_getD] at hf
  have flat : (xs.map (binary b)).flatten=CompetitorCountFold.raw b xs := by
    rw [CompetitorCountFold.raw,List.flatMap_def]
  simp only [List.length_map,List.nil_append,flat] at hr hf ht
  exact ⟨rc,hr,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,ht⟩

theorem after_word (a : WilliamsAlgorithm) (ds : List Datum) (S R B b : Nat) (xs : List Nat) :
    (after a ds S R B b xs).tapes (raw a)=CompetitorCountFold.raw b xs := by
  unfold after raw
  rw [RepairSource.CloseoutFinal.C10SupplierSelect.cfg_tapes_castAdd]
  exact P1TopDownPaidReusable.source_output a ds S R B _ _


private theorem cfg_heads {t st : Nat} (phase : Fin 5) (data : Configuration t st)
    (N h : Nat) (i : Fin t) : (RepeatMachine.cfg phase data N h).heads (i.castAdd 1)=data.heads i := by
  simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config]

theorem after_head (a : WilliamsAlgorithm) (ds : List Datum) (S R B b : Nat) (xs : List Nat) :
    (after a ds S R B b xs).heads (raw a)=(CompetitorCountFold.raw b xs).length := by
  unfold after raw
  rw [cfg_heads]
  simp only [source,outputSlot,P1TopDownPaidReusable.heads,P1TopDownPaidReusableBody.heads,
    P1Closure.RawRowJoin.heads,Fin.addCases_left,Fin.addCases_right,Matrix.cons_val_zero]

set_option maxHeartbeats 1000000 in
theorem run (a : WilliamsAlgorithm) (ds : List Datum) (dflt : Datum) (S R B b v : Nat) (xs : List Nat)
    (hv : ∀ k (hk : k<ds.length),Valid a B R S ds[k])
    (hwords : ds.map Datum.emit=xs.map (binary b))
    (hw : b ≤ v) (hx : ∀ x∈xs,x<2^b) (hfit : xs.sum<2^v) :
    let e:=entry a ds S R B xs.length
    let f:=after a ds S R B b xs
    ∃ Z, Step (machine a) (budget a S b v xs.length)
      (Fin.addCases e.heads (fun _ : Fin 11=>0)) (Fin.addCases e.tapes (P1TopDownPaidFamilySum.extra b v xs.length))
      (P1TopDownPaidFamilySum.finalHeads (raw a) f.heads)
      (P1TopDownPaidFamilySum.final (raw a) f.tapes b v xs Z) ∧
      P1TopDownPaidFamilySum.final (raw a) f.tapes b v xs Z
        (P1TopDownPaidFamilySum.sumSlots (raw a) 5)=frame (binary v xs.sum) ∧
      (∀ i,P1TopDownPaidFamilySum.final (raw a) f.tapes b v xs Z (i.castAdd 11)=f.tapes i) := by
  dsimp only
  have first:=(family_run a ds dflt S R B b xs hv hwords).embed
    (fun _ : Fin 11=>0) (P1TopDownPaidFamilySum.extra b v xs.length)
  obtain ⟨Z,last,value,old,_⟩:=P1TopDownPaidFamilySum.run (raw a)
    (after a ds S R B b xs).heads (after a ds S R B b xs).tapes b v xs
    (after_head a ds S R B b xs) (after_word a ds S R B b xs) hw hx hfit
  exact ⟨Z,first.seq last,value,old⟩

end PCJ9856d3e73b1d4df0_.FamilySum

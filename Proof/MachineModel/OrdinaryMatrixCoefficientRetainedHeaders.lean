import Proof.MachineModel.OrdinaryMatrixMaskSemantics

/-! Additional physical fields of the existing coefficient header run.
This strengthens the receipt of the same machine; no parsing is repeated. -/
namespace NearCubicWires.RepairOrdinary.MatrixCoefficientRetainedHeaders
open LocalBitMultitape MatrixScoreBatch SignedSortKey RepairRepresentation
open MatrixCoefficientHeaders
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem headers_fields (r : Request) : ∃ actual,
    run machine (budget r) (input r)=some actual ∧
    actual.final.tapes 0=physicalInput r ∧ actual.final.heads 0=0 ∧
    actual.final.tapes 1=word r ∧ actual.final.heads 1=(header r).length ∧
    actual.final.tapes 12=UnaryTemplate.tape r.d ∧ actual.final.heads 12=1 ∧
    actual.final.tapes 32=UnaryTemplate.tape r.Gates ∧ actual.final.heads 32=1 ∧
    actual.final.tapes 22=UnaryTemplate.tape r.p ∧ actual.final.heads 22=1 ∧
    actual.steps≤budget r := by
  obtain ⟨base,hb,bt0,bh0,bt1,bh1,_,_,_,_,bd,bdh,_,_,_,_,bp,bph,bs⟩ :=
    MatrixScoreHeaders.headers_run r.d r.p (natWord r.Gates++r.cuts.flatMap (cutWord r.p))
  have he := TapeEmbedding.run_embed MatrixScoreHeaders.machine (fun _ : Fin 10 => 0)
    (fun _ : Fin 10 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 10 => 0) (fun _ : Fin 10 => []) base
  obtain ⟨body,hbody,sourceT,sourceH,_,_,_,_,_,_,gateT,gateH,bodyS⟩ := MatrixDimensionPrepare.prepare_run
    (natWord r.d++natWord r.p) (r.cuts.flatMap (cutWord r.p)) (natBitLength r.Gates) r.Gates
    (Nat.lt_pow_succ_log_self (by decide) r.Gates)
  have hsource : (natWord r.d++natWord r.p)++List.replicate (natBitLength r.Gates) true++
      false::(binary (natBitLength r.Gates) r.Gates++r.cuts.flatMap (cutWord r.p))=word r := by
    simp [word,header,WilliamsInputHeader.natWord_eq,List.append_assoc]
  have hpre : (natWord r.d++natWord r.p).length=2*natBitLength r.d+1+(2*natBitLength r.p+1) := by
    simp [WilliamsInputHeader.natWord_eq,Nat.add_assoc]
    omega
  rw [hsource] at hbody sourceT
  let entry : Configuration 11 WilliamsInputHeader.dimensionStates := Composition.leftConfig _ (MatrixDimensionPrepare.input (word r) (natWord r.d++natWord r.p).length)
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro j
      fin_cases j
      · simpa [prepared,TapeEmbedding.receipt,TapeEmbedding.config,slots,entry,Composition.leftConfig,
          MatrixDimensionPrepare.input,MatrixDimensionField.input,MatrixDimensionHeader.input,hpre,Fin.addCases] using bh1
      all_goals simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config,slots,entry,Composition.leftConfig,
        MatrixDimensionPrepare.input,MatrixDimensionField.input,MatrixDimensionHeader.input,Fin.addCases]
    · intro j
      fin_cases j
      · simpa [prepared,TapeEmbedding.receipt,TapeEmbedding.config,slots,entry,Composition.leftConfig,
          MatrixDimensionPrepare.input,MatrixDimensionField.input,MatrixDimensionHeader.input,Fin.addCases,
          word,header,List.append_assoc] using bt1
      all_goals simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config,slots,entry,Composition.leftConfig,
        MatrixDimensionPrepare.input,MatrixDimensionField.input,MatrixDimensionHeader.input,Fin.addCases]
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config slots slots_injective MatrixDimensionPrepare.machine
    prepared.final.heads prepared.final.tapes _ entry body hbody
  rw [hi] at hf
  have hj := Composition.run_join first last _ _ _ prepared focused he hf
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 10 => 0) (fun _ : Fin 10 => [])
      (initialConfiguration MatrixScoreHeaders.machine (MatrixScoreHeaders.input
        (natWord r.d++natWord r.p++(natWord r.Gates++r.cuts.flatMap (cutWord r.p))))))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,
        MatrixScoreHeaders.input,input,physicalInput,word,header,List.append_assoc,Fin.addCases]
  rw [hin] at hj
  have otherT (i : Fin 23) (hn : RecoveryFocus.pick slots (i.castAdd 10)=none) :
      focused.final.tapes (i.castAdd 10)=base.final.tapes i := by
    rw [ff]
    simp [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  have otherH (i : Fin 23) (hn : RecoveryFocus.pick slots (i.castAdd 10)=none) :
      focused.final.heads (i.castAdd 10)=base.final.heads i := by
    rw [ff]
    simp [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  have pick (j : Fin 11) : RecoveryFocus.pick slots (slots j)=some j := RecoveryFocus.pick_slot slots slots_injective j
  refine ⟨Composition.joinedReceipt prepared focused,hj,?_,(otherH 0 (by decide)).trans bh0,?_,?_,
    (otherT 12 (by decide)).trans bd,(otherH 12 (by decide)).trans bdh,?_,?_,
    (otherT 22 (by decide)).trans bp,(otherH 22 (by decide)).trans bph,?_⟩
  · exact (otherT 0 (by decide)).trans (by simpa only [physicalInput,word,header,List.append_assoc] using bt0)
  · change focused.final.tapes (slots 0)=_
    rw [ff]
    simpa only [RecoveryFocus.config,pick] using sourceT
  · change focused.final.heads (slots 0)=_
    rw [ff]
    simp only [RecoveryFocus.config,pick]
    simp [header,WilliamsInputHeader.natWord_eq,List.length_append,Nat.add_assoc] at sourceH ⊢
    omega
  · change focused.final.tapes (slots 10)=_
    rw [ff]
    simpa only [RecoveryFocus.config,pick] using gateT
  · change focused.final.heads (slots 10)=_
    rw [ff]
    simpa only [RecoveryFocus.config,pick] using gateH
  · change base.steps+1+focused.steps≤budget r
    rw [fs]
    unfold budget
    omega


end NearCubicWires.RepairOrdinary.MatrixCoefficientRetainedHeaders

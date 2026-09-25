import Proof.Packets.NormalizerCold
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding
namespace PCJ9eff70d512234a4c_Fixed.Materializer.Normalize
theorem prefix_run_width (B : Nat) (raw : List (List Bool)) (hw : ∀ bits∈raw,bits.length=B) :
    ∃ r,runFrom prefixMachine (prefixBudget B raw) (Composition.leftConfig _ (dedupEntry B raw))=some r ∧
      r.steps≤prefixBudget B raw ∧
      r.final.tapes 0=SuffixScan.stream (records raw) ∧ r.final.heads 0=0 ∧
      r.final.tapes 3=CompareMachine.word raw.length ∧ r.final.heads 3=1 ∧
      r.final.tapes 14=ParityFilter.candidateStream (candidates raw) ∧ r.final.heads 14=0 ∧
      r.final.tapes 11=CompareMachine.word (candidates raw).length ∧ r.final.heads 11=1 ∧
      (∀ i : Fin 11, 3 ≤ i.val → r.final.heads (i.natAdd 13)=extraHeads i ∧
        r.final.tapes (i.natAdd 13)=extraData B raw.length i) ∧
      r.final.tapes 13=UnaryTemplate.tape (2*B+3) := by
  obtain ⟨a,ha,has,a0,ah0,a2,ah2,a3,ah3,a11,ah11⟩ := DedupMaterialReady.ready_run [] (records raw)
  simp only [List.append_nil,records,List.length_map] at ha a0 a3
  have ae := TapeEmbedding.run_embed DedupMaterialReady.machine extraHeads (extraData B raw.length) _ _ a ha
  let first := TapeEmbedding.receipt extraHeads (extraData B raw.length) a
  have hab : MaskReverseReady.budget (2*B+3) (distinctBits raw).length≤reverseCap B raw.length := by
    have hn := (List.dedup_sublist raw).length_le
    simp only [distinctBits,List.length_map,reverseCap,MaskReverseReady.budget]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _
  obtain ⟨b,hb,hbs,b0,bh0,b1,bh1,b2,bh2,b3,bh3,_⟩ :=
    MaskReverseReady.ready_run (2*B+3) (distinctBits raw) [] [] [] (reverseCap B raw.length) (distinct_width B raw hw) hab
  have hh : ∀ j,first.final.heads (reverseSlots j)=
      (MaskReverseReady.input (2*B+3) (distinctBits raw).length 0 (distinctBits raw).flatten [] (reverseCap B raw.length)).heads j := by
    intro j; fin_cases j <;>
      simp [first,TapeEmbedding.receipt,TapeEmbedding.config,reverseSlots,extraHeads,
        MaskReverseReady.input,CursorReady.input,ZeroPadding.config,Rewind.recording,Rewind.config,
        Composition.leftConfig,MaskSeek.loopCfg,MaskSeek.cfg,RepeatMachine.cfg,controlConfig,
        Fin.addCases,ah2,ah11]
  have a2' : a.final.tapes 2=(distinctBits raw).flatten := a2.trans (distinct_flat raw).symm
  have a11' : a.final.tapes 11=CompareMachine.word (distinctBits raw).length := by
    rw [dedup_records] at a11
    simpa only [records,distinctBits,List.length_map] using a11
  have ht : ∀ j,first.final.tapes (reverseSlots j)=
      (MaskReverseReady.input (2*B+3) (distinctBits raw).length 0 (distinctBits raw).flatten [] (reverseCap B raw.length)).tapes j := by
    intro j; fin_cases j <;>
      simp [first,TapeEmbedding.receipt,TapeEmbedding.config,reverseSlots,extraData,
        MaskReverseReady.input,CursorReady.input,ZeroPadding.config,Rewind.recording,Rewind.config,
        Rewind.Workspace.capacities,ZeroPadding.pad,Composition.leftConfig,MaskSeek.loopCfg,MaskSeek.cfg,
        RepeatMachine.cfg,controlConfig,Fin.addCases,a2',a11']
  simp only [List.nil_append,List.append_nil,List.length_nil] at hb
  obtain ⟨c,hc,_,hcs,hch,hct,hother⟩ := RecoveryFocus.dock reverseSlots reverseSlots_injective
    MaskReverseReady.machine _ first.final.heads first.final.tapes _ hh ht b hb
  have hj : runFrom reverseMachine (2*MaskReverseReady.budget (2*B+3) (distinctBits raw).length+2)
      (Composition.restart first.final reverseMachine.start)=some c := hc
  have h := Composition.run_join dedupMachine reverseMachine _ _ _ first c ae hj
  have hlen : (distinctBits raw).length=raw.dedup.length := by simp only [distinctBits,List.length_map]
  rw [hlen] at h hbs
  refine ⟨_,h,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change first.steps+1+c.steps≤prefixBudget B raw
    rw [hcs]
    unfold prefixBudget
    change a.steps+1+b.steps≤_
    omega
  · change c.final.tapes 0=_
    rw [(hother 0 (by decide +kernel)).2]
    simpa [first,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,records] using a0
  · change c.final.heads 0=0
    rw [(hother 0 (by decide +kernel)).1]
    simpa [first,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using ah0
  · change c.final.tapes 3=_
    rw [(hother 3 (by decide +kernel)).2]
    simpa [first,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using a3
  · change c.final.heads 3=1
    rw [(hother 3 (by decide +kernel)).1]
    simpa [first,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using ah3
  · change c.final.tapes (reverseSlots 2)=_
    rw [hct,b2]
    simpa using distinct_reverse_flat raw
  · change c.final.heads (reverseSlots 2)=0
    rw [hch,bh2]
    rfl
  · change c.final.tapes (reverseSlots 3)=_
    rw [hct,b3]
    simp [candidates,distinctBits]
  · change c.final.heads (reverseSlots 3)=1
    rw [hch,bh3]
  · intro i hi
    have hn : ∀ j,reverseSlots j≠i.natAdd 13 := by
      intro j he
      have hv := congrArg Fin.val he
      fin_cases j
      · change 13=13+i.val at hv; omega
      · change 2=13+i.val at hv; omega
      · change 14=13+i.val at hv; omega
      · change 11=13+i.val at hv; omega
      · change 15=13+i.val at hv; omega
    change c.final.heads (i.natAdd 13)=_ ∧ c.final.tapes (i.natAdd 13)=_
    rw [(hother _ hn).1,(hother _ hn).2]
    exact ⟨TapeEmbedding.receipt_heads_new extraHeads (extraData B raw.length) a i,
      TapeEmbedding.receipt_tapes_new extraHeads (extraData B raw.length) a i⟩

  · change c.final.tapes (reverseSlots 0)=_
    rw [hct,b0]

theorem run_width (B : Nat) (raw : List (List Bool)) (hw : ∀ bits∈raw,bits.length=B) :
    ∃ r,runFrom machine (budget B raw) (entry B raw)=some r ∧ r.steps≤budget B raw ∧
      r.final.tapes 20=(NormalizerOrder.ordered raw).flatten ∧ r.final.heads 20=0 ∧
      r.final.tapes 21=CompareMachine.word (NormalizerOrder.ordered raw).length ∧ r.final.heads 21=1 ∧
      r.final.tapes 13=UnaryTemplate.tape (2*B+3) := by
  obtain ⟨a,ha,has,a0,ah0,a3,ah3,a14,ah14,a11,ah11,aextra,aWidth⟩ := prefix_run_width B raw hw
  have hfits := filter_fits B raw
  obtain ⟨b,hb,hbs,bout,boutHead,bcount,bcountHead,_⟩ := ParityFilter.ready_run B (candidates raw)
    [] [] [] [] [] (records raw) 0 (probeCap B) (scanCap B raw.length)
    (filterCap B raw.length) (countCap B raw.length) false false (candidate_width B raw hw) (probes_fit B raw hw)
    (by simp [records,scanCap]) hfits (by unfold countCap; omega)
  have hh : ∀ j,a.final.heads (filterSlots j)=
      (ParityFilter.readyInput B (candidates raw) [] [] [] [] [] (records raw) 0
        (probeCap B) (scanCap B raw.length) (filterCap B raw.length) (countCap B raw.length) false false).heads j := by
    rw [filter_input_heads]
    intro j; fin_cases j
    · exact ah14
    · exact ah0
    · exact (aextra 3 (by decide)).1
    · exact (aextra 4 (by decide)).1
    · exact (aextra 5 (by decide)).1
    · exact ah3
    · exact (aextra 6 (by decide)).1
    · exact (aextra 7 (by decide)).1
    · exact (aextra 8 (by decide)).1
    · exact ah11
    · exact (aextra 9 (by decide)).1
    · exact (aextra 10 (by decide)).1
  have ht : ∀ j,a.final.tapes (filterSlots j)=
      (ParityFilter.readyInput B (candidates raw) [] [] [] [] [] (records raw) 0
        (probeCap B) (scanCap B raw.length) (filterCap B raw.length) (countCap B raw.length) false false).tapes j := by
    rw [filter_input_tapes]
    intro j; fin_cases j
    · exact a14
    · exact a0
    · exact (aextra 3 (by decide)).2
    · exact (aextra 4 (by decide)).2
    · exact (aextra 5 (by decide)).2
    · exact a3
    · exact (aextra 6 (by decide)).2
    · exact (aextra 7 (by decide)).2
    · exact (aextra 8 (by decide)).2
    · exact a11
    · exact (aextra 9 (by decide)).2
    · exact (aextra 10 (by decide)).2
  obtain ⟨c,hc,_,hcs,hch,hct,hother⟩ := RecoveryFocus.dock filterSlots filterSlots_injective
    ParityFilter.readyMachine _ a.final.heads a.final.tapes _ hh ht b hb
  have hj : runFrom filterMachine
      (4*ParityFilter.filterBudget B (records raw).length (candidates raw).length (probeCap B)+6)
      (Composition.restart a.final filterMachine.start)=some c := hc
  have h := Composition.run_join prefixMachine filterMachine _ _ _ a c ha hj
  have htime : prefixBudget B raw+1+
      (4*ParityFilter.filterBudget B (records raw).length (candidates raw).length (probeCap B)+6)≤budget B raw := by
    unfold budget; omega
  have more := runFrom_moreFuel machine _
    (budget B raw-(prefixBudget B raw+1+
      (4*ParityFilter.filterBudget B (records raw).length (candidates raw).length (probeCap B)+6))) _ _ h
  rw [Nat.add_sub_of_le htime] at more
  refine ⟨_,more,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+c.steps≤budget B raw
    rw [hcs]
    unfold budget
    omega
  · change c.final.tapes (filterSlots 7)=_
    rw [hct,bout]
    simp only [List.nil_append,selected_eq]
  · change c.final.heads (filterSlots 7)=0
    rw [hch,boutHead]
    rfl
  · change c.final.tapes (filterSlots 8)=_
    rw [hct,bcount]
    simp only [selected_eq,Nat.zero_add]
  · change c.final.heads (filterSlots 8)=1
    rw [hch,bcountHead]

  · change c.final.tapes 13=_
    rw [(hother 13 (by decide +kernel)).2,aWidth]

end PCJ9eff70d512234a4c_Fixed.Materializer.Normalize
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizeCold
theorem seeded_run_width (B : Nat) (raw : List (List Bool)) (hw : ∀ bits∈raw,bits.length=B) :
    ∃ r,runFrom Normalize.machine (Normalize.budget B raw) (seededEntry B raw)=some r ∧
      r.steps≤Normalize.budget B raw ∧
      r.final.tapes 20=(NormalizerOrder.ordered raw).flatten ∧ r.final.heads 20=0 ∧
      r.final.tapes 21=CompareMachine.word (NormalizerOrder.ordered raw).length ∧ r.final.heads 21=1 ∧
      r.final.tapes 13=UnaryTemplate.tape (2*B+3) := by
  obtain ⟨a,ha,has,aout,ahout,acount,ahcount,aWidth⟩ := Normalize.run_width B raw hw
  rw [←padded_entry] at ha
  obtain ⟨r,hr,hrf,hrs,_⟩ := ZeroPadding.run_unpad Normalize.machine (capacities B raw.length) _ _ a ha
  refine ⟨r,hr,hrs.le.trans has,?_,?_,?_,?_,?_⟩
  · have h := congrArg (fun c=>c.tapes 20) hrf
    simpa [ZeroPadding.config,capacities,aout] using h
  · have h := congrArg (fun c=>c.heads 20) hrf
    simpa [ZeroPadding.config,ahout] using h
  · have h := congrArg (fun c=>c.tapes 21) hrf
    simpa [ZeroPadding.config,capacities,acount] using h
  · have h := congrArg (fun c=>c.heads 21) hrf
    simpa [ZeroPadding.config,ahcount] using h


  · have h := congrArg (fun c=>c.tapes 13) hrf
    simpa [ZeroPadding.config,capacities,aWidth] using h

theorem run_width (B : Nat) (raw : List (List Bool)) (hw : ∀ bits∈raw,bits.length=B) :
    ∃ r,runFrom machine (budget B raw) (entry B raw)=some r ∧ r.steps≤budget B raw ∧
      r.final.tapes 20=(NormalizerOrder.ordered raw).flatten ∧ r.final.heads 20=0 ∧
      r.final.tapes 21=CompareMachine.word (NormalizerOrder.ordered raw).length ∧ r.final.heads 21=1 ∧
      r.final.tapes 13=UnaryTemplate.tape (2*B+3) := by
  obtain ⟨a,ha,haf,has⟩ := boot_run B raw
  obtain ⟨b,hb,hbs,bout,bhout,bcount,bhcount,bWidth⟩ := seeded_run_width B raw hw
  have hj : runFrom Normalize.machine (Normalize.budget B raw)
      (Composition.restart a.final Normalize.machine.start)=some b := by
    rw [haf]
    exact hb
  have h := Composition.run_join boot Normalize.machine _ _ _ a b ha hj
  have ht : 1+1+Normalize.budget B raw=budget B raw := by unfold budget; omega
  rw [ht] at h
  refine ⟨_,h,?_,bout,bhout,bcount,bhcount,bWidth⟩
  change a.steps+1+b.steps≤budget B raw
  rw [has]
  unfold budget
  omega

end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizeCold

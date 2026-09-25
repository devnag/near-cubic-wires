import Proof.Packets.NormalizerMaterializeData

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.Normalize
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding

def prefixBudget (B : Nat) (raw : List (List Bool)) :=
  DedupMaterialReady.budget (records raw)+1+(2*MaskReverseReady.budget (2*B+3) raw.dedup.length+2)

/-- The actual deduplication and reversing stages expose an ordered candidate
bank and retain the original polynomial and its actual count driver. -/
theorem prefix_run (B : Nat) (raw : List (List Bool)) (hw : ∀ bits∈raw,bits.length=B) :
    ∃ r,runFrom prefixMachine (prefixBudget B raw) (Composition.leftConfig _ (dedupEntry B raw))=some r ∧
      r.steps≤prefixBudget B raw ∧
      r.final.tapes 0=SuffixScan.stream (records raw) ∧ r.final.heads 0=0 ∧
      r.final.tapes 3=CompareMachine.word raw.length ∧ r.final.heads 3=1 ∧
      r.final.tapes 14=ParityFilter.candidateStream (candidates raw) ∧ r.final.heads 14=0 ∧
      r.final.tapes 11=CompareMachine.word (candidates raw).length ∧ r.final.heads 11=1 ∧
      (∀ i : Fin 11, 3 ≤ i.val → r.final.heads (i.natAdd 13)=extraHeads i ∧
        r.final.tapes (i.natAdd 13)=extraData B raw.length i) := by
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
  refine ⟨_,h,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
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

end PCJ9eff70d512234a4c_Fixed.Materializer.Normalize

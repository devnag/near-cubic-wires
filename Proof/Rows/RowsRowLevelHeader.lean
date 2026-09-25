import Proof.Rows.RowsRowLevelFields
import Proof.Rows.HeaderRewind

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsRowLevel
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.P1Closure NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

/-! ## 1. The cold family writer's final bank, port class by port class -/

section Cold
variable {l r : Nat} (gs : List (ExactThresholdGate (l+r))) [P1Radix gs] (Q w : Nat)
  (ps : List (List (List (Fin gs.length)))) (out pre tail : List Bool)

theorem cold_tapes_native (k : Fin 277) (hk : ∀ i,NativeFanoutLayout.bank i≠k) :
    CompactColdFamily.finalTapes gs Q w ps out pre tail (CompactNativeInitialize.native k)=
      CompactColdFamily.ambient gs Q w ps out pre tail (CompactNativeInitialize.native k) := by
  have hx : CompactNativeInitialize.native k=CompactColdFamily.loopSlots (k.castAdd 1) := rfl
  rw [hx,CompactColdFamily.finalTapes,install_slot _ CompactColdFamily.loopSlots_injective]
  simp only [CompactColdFamily.finalConfig,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    Fin.addCases_left,P1CompactNativeFamily.entry,P1CompactNativeState.tapes]
  rw [install_other _ _ _ _ hk]
  rfl

theorem cold_heads_native (k : Fin 277) (hk : ∀ i,NativeFanoutLayout.bank i≠k) :
    CompactColdFamily.finalHeads gs Q w ps out pre tail (CompactNativeInitialize.native k)=
      CompactColdFamily.ambientH out pre (CompactNativeInitialize.native k) := by
  have hx : CompactNativeInitialize.native k=CompactColdFamily.loopSlots (k.castAdd 1) := rfl
  rw [hx,CompactColdFamily.finalHeads,dockH_slot _ CompactColdFamily.loopSlots_injective]
  simp only [CompactColdFamily.finalConfig,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    Fin.addCases_left,P1CompactNativeFamily.entry,P1CompactNativeState.heads]
  rw [dockH_other _ _ _ _ hk]
  rfl

theorem bank_ne_source (i : Fin 128) (j : Fin 15) :
    NativeFanoutLayout.bank i≠NativeFanoutLayout.sources j := by
  revert i j
  decide

/-- The fifteen fanout masters survive the whole family loop. -/
theorem cold_source_tapes (j : Fin 15) :
    CompactColdFamily.finalTapes gs Q w ps out pre tail
      (CompactNativeInitialize.native (NativeFanoutLayout.sources j))=
      P1CompactNativeMaster.words gs Q w j := by
  rw [cold_tapes_native gs Q w ps out pre tail _ (fun i=>bank_ne_source i j)]
  have hp : CompactNativeInitialize.native (NativeFanoutLayout.sources j)=
      CompactNativeInitialize.ports ((j.castAdd (124+1)).castAdd 1) := by
    simp only [CompactNativeInitialize.ports,Function.comp_apply,NativeFanoutLayout.ports,
      Fin.addCases_left]
  rw [hp,CompactColdFamily.ambient,CompactNativeInitialize.output_ports]
  simp only [NativeFanout.output,Fin.addCases_left]

theorem cold_source_heads (j : Fin 15) :
    CompactColdFamily.finalHeads gs Q w ps out pre tail
      (CompactNativeInitialize.native (NativeFanoutLayout.sources j))=0 := by
  rw [cold_heads_native gs Q w ps out pre tail _ (fun i=>bank_ne_source i j)]
  have h : ∀ j : Fin 15,CompactNativeInitialize.native (NativeFanoutLayout.sources j)≠180 ∧
      CompactNativeInitialize.native (NativeFanoutLayout.sources j)≠262 ∧
      CompactNativeInitialize.native (NativeFanoutLayout.sources j)≠277 := by decide
  simp only [CompactColdFamily.ambientH,CompactNativeInitialize.heads,if_neg (h j).1,
    if_neg (h j).2.1,if_neg (h j).2.2]

/-- Final raw position and output after all packets of the row. -/
abbrev finalPos : Nat := pre.length+(ps.flatMap P1CompactNativeFamily.rawWord).length
abbrev finalOut : List Bool := out++ps.flatMap (P1CompactNativeFamily.emit gs Q w)

theorem cold_bank_tapes (i : Fin 128) :
    CompactColdFamily.finalTapes gs Q w ps out pre tail
      (CompactNativeInitialize.native (NativeFanoutLayout.bank i))=
      NativeInitializedPorts.word (P1CompactNativeMaster.words gs Q w)
        (P1CompactNativeMeasured.capacity gs Q w)
        (pre++ps.flatMap P1CompactNativeFamily.rawWord++tail) (finalOut gs Q w ps out) i := by
  have hx : CompactNativeInitialize.native (NativeFanoutLayout.bank i)=
      CompactColdFamily.loopSlots ((NativeFanoutLayout.bank i).castAdd 1) := rfl
  rw [hx,CompactColdFamily.finalTapes,install_slot _ CompactColdFamily.loopSlots_injective]
  simp only [CompactColdFamily.finalConfig,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    Fin.addCases_left,P1CompactNativeFamily.entry,P1CompactNativeState.tapes]
  rw [install_slot _ NativeFanoutLayout.bank_injective]

theorem cold_bank_heads (i : Fin 128) :
    CompactColdFamily.finalHeads gs Q w ps out pre tail
      (CompactNativeInitialize.native (NativeFanoutLayout.bank i))=
      NativeInitialize.extraH (finalPos gs ps pre) (finalOut gs Q w ps out) i := by
  have hx : CompactNativeInitialize.native (NativeFanoutLayout.bank i)=
      CompactColdFamily.loopSlots ((NativeFanoutLayout.bank i).castAdd 1) := rfl
  rw [hx,CompactColdFamily.finalHeads,dockH_slot _ CompactColdFamily.loopSlots_injective]
  simp only [CompactColdFamily.finalConfig,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    Fin.addCases_left,P1CompactNativeFamily.entry,P1CompactNativeState.heads]
  rw [dockH_slot _ NativeFanoutLayout.bank_injective,List.take_length]

theorem cold_counter_tapes :
    CompactColdFamily.finalTapes gs Q w ps out pre tail 277=CompareMachine.word ps.length := by
  have hx : (277 : Fin 440)=CompactColdFamily.loopSlots ((0 : Fin 1).natAdd 277) := rfl
  rw [hx,CompactColdFamily.finalTapes,install_slot _ CompactColdFamily.loopSlots_injective]
  simp only [CompactColdFamily.finalConfig,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    Fin.addCases_right]

theorem cold_counter_heads :
    CompactColdFamily.finalHeads gs Q w ps out pre tail 277=1 := by
  have hx : (277 : Fin 440)=CompactColdFamily.loopSlots ((0 : Fin 1).natAdd 277) := rfl
  rw [hx,CompactColdFamily.finalHeads,dockH_slot _ CompactColdFamily.loopSlots_injective]
  simp only [CompactColdFamily.finalConfig,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    Fin.addCases_right]

theorem cold_outer_tapes (x : Fin 440) (hx : 278 ≤ x.val) :
    CompactColdFamily.finalTapes gs Q w ps out pre tail x=
      CompactColdFamily.ambient gs Q w ps out pre tail x := by
  rw [CompactColdFamily.finalTapes,install_other _ _ _ _ (fun i he=>by
    have hv := congrArg Fin.val he
    change i.val=x.val at hv
    have := i.isLt
    omega)]

theorem cold_outer_heads (x : Fin 440) (hx : 278 ≤ x.val) :
    CompactColdFamily.finalHeads gs Q w ps out pre tail x=0 := by
  rw [CompactColdFamily.finalHeads,dockH_other _ _ _ _ (fun i he=>by
    have hv := congrArg Fin.val he
    change i.val=x.val at hv
    have := i.isLt
    omega)]
  have h180 : x≠180 := fun he=>by rw [he] at hx; exact absurd hx (by decide)
  have h262 : x≠262 := fun he=>by rw [he] at hx; exact absurd hx (by decide)
  have h277 : x≠277 := fun he=>by rw [he] at hx; exact absurd hx (by decide)
  simp only [CompactColdFamily.ambientH,CompactNativeInitialize.heads,if_neg h180,if_neg h262,
    if_neg h277]

/-- The three retained metadata inputs outside the native bank survive the metadata writer. -/
theorem meta_keep0 (B n N b D Q w : Nat) (cache : List Bool) :
    CompactMetadata.output B n N b D Q w cache 0=List.replicate B true := by
  change CompactMetadata.data8 B n N b D Q w cache 0=_
  rw [CompactMetadata.data8_other _ _ _ _ _ _ _ _ 0 (by decide),
    CompactMetadata.data7_other _ _ _ _ _ _ _ _ 0 (by decide),
    CompactMetadata.data6_other _ _ _ _ _ _ _ _ 0 (by decide),
    CompactMetadata.data5_other _ _ _ _ _ _ _ _ 0 (by decide),
    CompactMetadata.data4_other _ _ _ _ _ _ _ _ 0 (by decide),
    CompactMetadata.data3_other _ _ _ _ _ _ _ _ 0 (by decide),
    CompactMetadata.data2_other _ _ _ _ _ _ _ _ 0 (by decide),
    show (0 : Fin 162)=CompactMetadata.slots1 0 from rfl,CompactMetadata.data1_slot]
  rfl

theorem meta_keep4 (B n N b D Q w : Nat) (cache : List Bool) :
    CompactMetadata.output B n N b D Q w cache 4=UnaryTemplate.tape D := by
  change CompactMetadata.data8 B n N b D Q w cache 4=_
  rw [CompactMetadata.data8_other _ _ _ _ _ _ _ _ 4 (by decide),
    CompactMetadata.data7_other _ _ _ _ _ _ _ _ 4 (by decide),
    CompactMetadata.data6_other _ _ _ _ _ _ _ _ 4 (by decide),
    CompactMetadata.data5_other _ _ _ _ _ _ _ _ 4 (by decide),
    CompactMetadata.data4_other _ _ _ _ _ _ _ _ 4 (by decide),
    show (4 : Fin 162)=CompactMetadata.slots3 1 from rfl,CompactMetadata.data3_slot]
  rfl

theorem meta_keep5 (B n N b D Q w : Nat) (cache : List Bool) :
    CompactMetadata.output B n N b D Q w cache 5=UnaryTemplate.tape Q := by
  change CompactMetadata.data8 B n N b D Q w cache 5=_
  rw [show (5 : Fin 162)=CompactMetadata.slots8 2 from rfl,CompactMetadata.data8_slot]
  have h := (CompactMetadata.short_spec n w Q).2.1 (2 : Fin 13)
  change CompactMetadata.shortOutput n w Q 2=_
  rw [show (2 : Fin 17)=(2 : Fin 13).castAdd 4 from rfl,h]
  rfl

/-- **The ten retained Header words survive the Header stage** (C4's `hkeep`, cold form). -/
theorem cold_retained_tapes (k : Fin 440) (hk : PCJ45bee56da9f34d5a_HeaderErase.retained k) :
    CompactColdFamily.finalTapes gs Q w ps out pre tail k=
      CompactNativeInitialize.input gs Q w ps.length (CompactColdFamily.source gs ps pre tail) out k := by
  unfold PCJ45bee56da9f34d5a_HeaderErase.retained at hk
  rcases hk with h|h|h|h|h|h|h|h|h|h
  · obtain rfl : k=(0 : Fin 440) := Fin.ext h
    change CompactColdFamily.finalTapes gs Q w ps out pre tail
      (CompactNativeInitialize.native (NativeFanoutLayout.sources 0))=_
    rw [cold_source_tapes,CompactNativeInitialize.input,
      show (0 : Fin 440)=CompactNativeInitialize.metadataSlots 7 from rfl,
      install_slot _ CompactNativeInitialize.meta_injective]
    rfl
  · obtain rfl : k=(3 : Fin 440) := Fin.ext h
    change CompactColdFamily.finalTapes gs Q w ps out pre tail
      (CompactNativeInitialize.native (NativeFanoutLayout.sources 3))=_
    rw [cold_source_tapes,CompactNativeInitialize.input,
      show (3 : Fin 440)=CompactNativeInitialize.metadataSlots 1 from rfl,
      install_slot _ CompactNativeInitialize.meta_injective]
    rfl
  · obtain rfl : k=(4 : Fin 440) := Fin.ext h
    change CompactColdFamily.finalTapes gs Q w ps out pre tail
      (CompactNativeInitialize.native (NativeFanoutLayout.sources 8))=_
    rw [cold_source_tapes,CompactNativeInitialize.input,
      show (4 : Fin 440)=CompactNativeInitialize.metadataSlots 2 from rfl,
      install_slot _ CompactNativeInitialize.meta_injective]
    rfl
  · obtain rfl : k=(15 : Fin 440) := Fin.ext h
    change CompactColdFamily.finalTapes gs Q w ps out pre tail
      (CompactNativeInitialize.native (NativeFanoutLayout.sources 1))=_
    rw [cold_source_tapes,CompactNativeInitialize.input,
      show (15 : Fin 440)=CompactNativeInitialize.metadataSlots 3 from rfl,
      install_slot _ CompactNativeInitialize.meta_injective]
    rfl
  · obtain rfl : k=(88 : Fin 440) := Fin.ext h
    change CompactColdFamily.finalTapes gs Q w ps out pre tail
      (CompactNativeInitialize.native (NativeFanoutLayout.sources 12))=_
    rw [cold_source_tapes,CompactNativeInitialize.input,
      show (88 : Fin 440)=CompactNativeInitialize.metadataSlots 6 from rfl,
      install_slot _ CompactNativeInitialize.meta_injective]
    rfl
  · obtain rfl : k=(262 : Fin 440) := Fin.ext h
    change CompactColdFamily.finalTapes gs Q w ps out pre tail
      (CompactNativeInitialize.native (NativeFanoutLayout.bank 113))=_
    rw [cold_bank_tapes,CompactNativeInitialize.input,
      install_other _ _ _ _ (by decide)]
    rfl
  · obtain rfl : k=(277 : Fin 440) := Fin.ext h
    rw [cold_counter_tapes,CompactNativeInitialize.input,install_other _ _ _ _ (by decide)]
    rfl
  · obtain rfl : k=(278 : Fin 440) := Fin.ext h
    have hp : ∀ j,CompactNativeInitialize.ports j≠278 := by
      intro j he
      have hv := congrArg Fin.val he
      change (NativeFanoutLayout.ports j).val=278 at hv
      have := (NativeFanoutLayout.ports j).isLt
      omega
    rw [cold_outer_tapes _ _ _ _ _ _ _ _ (by decide),CompactColdFamily.ambient,
      CompactNativeInitialize.output,install_other _ _ _ _ hp,CompactNativeInitialize.middle,
      CompactNativeInitialize.input,
      show (278 : Fin 440)=CompactNativeInitialize.metadataSlots 0 from rfl,
      install_slot _ CompactNativeInitialize.meta_injective,
      install_slot _ CompactNativeInitialize.meta_injective,meta_keep0]
    rfl
  · obtain rfl : k=(282 : Fin 440) := Fin.ext h
    have hp : ∀ j,CompactNativeInitialize.ports j≠282 := by
      intro j he
      have hv := congrArg Fin.val he
      change (NativeFanoutLayout.ports j).val=282 at hv
      have := (NativeFanoutLayout.ports j).isLt
      omega
    rw [cold_outer_tapes _ _ _ _ _ _ _ _ (by decide),CompactColdFamily.ambient,
      CompactNativeInitialize.output,install_other _ _ _ _ hp,CompactNativeInitialize.middle,
      CompactNativeInitialize.input,
      show (282 : Fin 440)=CompactNativeInitialize.metadataSlots 4 from rfl,
      install_slot _ CompactNativeInitialize.meta_injective,
      install_slot _ CompactNativeInitialize.meta_injective,meta_keep4]
    rfl
  · obtain rfl : k=(283 : Fin 440) := Fin.ext h
    have hp : ∀ j,CompactNativeInitialize.ports j≠283 := by
      intro j he
      have hv := congrArg Fin.val he
      change (NativeFanoutLayout.ports j).val=283 at hv
      have := (NativeFanoutLayout.ports j).isLt
      omega
    rw [cold_outer_tapes _ _ _ _ _ _ _ _ (by decide),CompactColdFamily.ambient,
      CompactNativeInitialize.output,install_other _ _ _ _ hp,CompactNativeInitialize.middle,
      CompactNativeInitialize.input,
      show (283 : Fin 440)=CompactNativeInitialize.metadataSlots 5 from rfl,
      install_slot _ CompactNativeInitialize.meta_injective,
      install_slot _ CompactNativeInitialize.meta_injective,meta_keep5]
    rfl

/-- The ten retained Header heads are the ambient heads after the whole row's raw word. -/
theorem cold_retained_heads (k : Fin 440) (hk : PCJ45bee56da9f34d5a_HeaderErase.retained k) :
    CompactColdFamily.finalHeads gs Q w ps out pre tail k=
      CompactColdFamily.ambientH out (pre++ps.flatMap P1CompactNativeFamily.rawWord) k := by
  unfold PCJ45bee56da9f34d5a_HeaderErase.retained at hk
  rcases hk with h|h|h|h|h|h|h|h|h|h
  · obtain rfl : k=(0 : Fin 440) := Fin.ext h
    exact (cold_source_heads gs Q w ps out pre tail 0).trans rfl
  · obtain rfl : k=(3 : Fin 440) := Fin.ext h
    exact (cold_source_heads gs Q w ps out pre tail 3).trans rfl
  · obtain rfl : k=(4 : Fin 440) := Fin.ext h
    exact (cold_source_heads gs Q w ps out pre tail 8).trans rfl
  · obtain rfl : k=(15 : Fin 440) := Fin.ext h
    exact (cold_source_heads gs Q w ps out pre tail 1).trans rfl
  · obtain rfl : k=(88 : Fin 440) := Fin.ext h
    exact (cold_source_heads gs Q w ps out pre tail 12).trans rfl
  · obtain rfl : k=(262 : Fin 440) := Fin.ext h
    change CompactColdFamily.finalHeads gs Q w ps out pre tail
      (CompactNativeInitialize.native (NativeFanoutLayout.bank 113))=_
    rw [cold_bank_heads]
    simp only [NativeInitialize.extraH,CompactColdFamily.ambientH,CompactNativeInitialize.heads,
      List.length_append]
    rfl
  · obtain rfl : k=(277 : Fin 440) := Fin.ext h
    rw [cold_counter_heads]
    rfl
  · obtain rfl : k=(278 : Fin 440) := Fin.ext h
    rw [cold_outer_heads _ _ _ _ _ _ _ _ (by decide)]
    rfl
  · obtain rfl : k=(282 : Fin 440) := Fin.ext h
    rw [cold_outer_heads _ _ _ _ _ _ _ _ (by decide)]
    rfl
  · obtain rfl : k=(283 : Fin 440) := Fin.ext h
    rw [cold_outer_heads _ _ _ _ _ _ _ _ (by decide)]
    rfl

end Cold

/-! ## 2. A Step's heads move at most one cell per step -/

theorem step_head_le {t s : Nat} {p : Machine t s} {n : Nat} {H J : Fin t → Nat}
    {A B : Fin t → List Bool} (run : Step p n H A J B) (i : Fin t) : J i ≤ H i+n := by
  obtain ⟨r,hr,rh,_,rs⟩ := run
  have h := SelectiveReset.prefix_head (prefix_of_run p n _ r hr).1 i
  rw [rh] at h
  change J i ≤ H i+r.steps at h
  omega

/-! ## 3. The accepted Header's final bank at one row -/

section Row
open PCJ9eff70d512234a4c_Fixed
variable {q Lq : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q Lq)
  (g : Packets.Geometry F) (layout : Packets.Layout a F g)
  (r : Packets.Row F.occurrences Lq) (pre tail : List Bool)

/-- **C2 driver 0**: Header port 53 is the unary scalar width `1^p` of the row's datum. -/
theorem header53_tapes (hr : r∈F.rows) (facts : Packets.PacketFacts a F g r) :
    PCJcc051fd4c1bd4540_Header.finalTapes a F g layout r [] pre tail 53=
      List.replicate (Packets.datum a F g layout r hr facts).row.p true := by
  letI := Packets.radix a F g layout
  change CompactColdFamily.finalTapes (Packets.pool a F g) ((Packets.live F).card+1) layout.w
    (Packets.packets a F g r) [] pre tail
    (CompactNativeInitialize.native (NativeFanoutLayout.sources 13))=_
  rw [cold_source_tapes]
  rfl

/-- **C2 driver 1**: Header port 3 is the arity template `UnaryTemplate.tape n`. -/
theorem header3_tapes :
    PCJcc051fd4c1bd4540_Header.finalTapes a F g layout r [] pre tail 3=
      UnaryTemplate.tape ((Packets.residual F+1)/2+Packets.residual F/2) := by
  letI := Packets.radix a F g layout
  change CompactColdFamily.finalTapes (Packets.pool a F g) ((Packets.live F).card+1) layout.w
    (Packets.packets a F g r) [] pre tail
    (CompactNativeInitialize.native (NativeFanoutLayout.sources 3))=_
  rw [cold_source_tapes]
  rfl

/-- **C2 driver 2**: Header port 141 is the sentinel word `false :: 1^Q`. -/
theorem header141_tapes :
    PCJcc051fd4c1bd4540_Header.finalTapes a F g layout r [] pre tail 141=
      CompareMachine.word ((Packets.live F).card+1) := by
  letI := Packets.radix a F g layout
  change CompactColdFamily.finalTapes (Packets.pool a F g) ((Packets.live F).card+1) layout.w
    (Packets.packets a F g r) [] pre tail
    (CompactNativeInitialize.native (NativeFanoutLayout.sources 14))=_
  rw [cold_source_tapes]
  rfl

/-- The three driver heads are at `0`. -/
theorem header_driver_heads :
    PCJcc051fd4c1bd4540_Header.finalHeads a F g layout r [] pre tail 53=0 ∧
    PCJcc051fd4c1bd4540_Header.finalHeads a F g layout r [] pre tail 3=0 ∧
    PCJcc051fd4c1bd4540_Header.finalHeads a F g layout r [] pre tail 141=0 := by
  letI := Packets.radix a F g layout
  refine ⟨?_,?_,?_⟩
  · change CompactColdFamily.finalHeads (Packets.pool a F g) ((Packets.live F).card+1) layout.w
      (Packets.packets a F g r) [] pre tail
      (CompactNativeInitialize.native (NativeFanoutLayout.sources 13))=_
    exact cold_source_heads _ _ _ _ _ _ _ _
  · change CompactColdFamily.finalHeads (Packets.pool a F g) ((Packets.live F).card+1) layout.w
      (Packets.packets a F g r) [] pre tail
      (CompactNativeInitialize.native (NativeFanoutLayout.sources 3))=_
    exact cold_source_heads _ _ _ _ _ _ _ _
  · change CompactColdFamily.finalHeads (Packets.pool a F g) ((Packets.live F).card+1) layout.w
      (Packets.packets a F g r) [] pre tail
      (CompactNativeInitialize.native (NativeFanoutLayout.sources 14))=_
    exact cold_source_heads _ _ _ _ _ _ _ _

/-- **C1 source**: Header port 180 holds exactly the datum's Header stream. -/
theorem header180_tapes (hr : r∈F.rows) (facts : Packets.PacketFacts a F g r) :
    PCJcc051fd4c1bd4540_Header.finalTapes a F g layout r [] pre tail 180=
      CloseoutRowsEstimator.Header.stream (Packets.datum a F g layout r hr facts).row := by
  rw [(PCJcc051fd4c1bd4540_Header.run a F g layout r hr facts [] pre tail).2,List.nil_append]

/-- **C1 source head**: the stream head is parked at its end. -/
theorem header180_heads (hr : r∈F.rows) (facts : Packets.PacketFacts a F g r) :
    PCJcc051fd4c1bd4540_Header.finalHeads a F g layout r [] pre tail 180=
      (CloseoutRowsEstimator.Header.stream (Packets.datum a F g layout r hr facts).row).length := by
  letI := Packets.radix a F g layout
  change CompactColdFamily.finalHeads (Packets.pool a F g) ((Packets.live F).card+1) layout.w
    (Packets.packets a F g r) [] pre tail
    (CompactNativeInitialize.native (NativeFanoutLayout.bank 31))=_
  rw [cold_bank_heads]
  change ([]++(Packets.packets a F g r).flatMap
    (P1CompactNativeFamily.emit (Packets.pool a F g) ((Packets.live F).card+1) layout.w)).length=_
  rw [List.nil_append,←PCJcc051fd4c1bd4540_Header.stream_eq a F g layout r hr facts]
  rfl

end Row


end
end RowsRowLevel

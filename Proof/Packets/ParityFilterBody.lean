import Proof.Packets.MaskSelect

/-! One actual candidate-normalization step. The coefficient is computed from
resident original records, then controls byte emission and the retained counter.
No machine, transition, coefficient bit, or run witness is an input premise. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ParityFilter
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding

abbrev scanSize := Fintype.card (RepeatMachine.Control PhysicalParityReuse.size)+2

def cfg {s : Nat} (q : Fin s) (candidate source out : List Bool)
    (cp sp kept cap count logCap : Nat) (eq found : Bool) : Configuration 9 s :=
  ⟨q,![cp,sp,0,0,0,1,0,out.length,kept+1],
    ![candidate,source,[eq],[found],List.replicate cap false,CompareMachine.word count,
      List.replicate logCap false,out,CompareMachine.word kept]⟩

def boot : Machine 9 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun i => if i=3 then some false else none,fun _ => .stay⟩ else none

noncomputable def scan : Machine 9 scanSize := TapeEmbedding.machine 2 PhysicalParityRestore.machine

def slots : Fin 4 → Fin 9 := ![0,7,8,3]
theorem slots_injective : Function.Injective slots := by decide +kernel

theorem pick_slots (i : Fin 9) : RecoveryFocus.pick slots i=
    ![some 0,none,none,some 3,none,none,none,some 1,some 2] i := by
  fin_cases i
  · exact RecoveryFocus.pick_slot slots slots_injective 0
  · exact dif_neg (by decide +kernel)
  · exact dif_neg (by decide +kernel)
  · exact RecoveryFocus.pick_slot slots slots_injective 3
  · exact dif_neg (by decide +kernel)
  · exact dif_neg (by decide +kernel)
  · exact dif_neg (by decide +kernel)
  · exact RecoveryFocus.pick_slot slots slots_injective 1
  · exact RecoveryFocus.pick_slot slots slots_injective 2

noncomputable def emit : Machine 9 6 := RecoveryFocus.machine slots MaskSelect.machine
noncomputable def tail := Composition.machine scan emit
noncomputable def body := Composition.machine boot tail
abbrev size := 2+(scanSize+6)

theorem boot_step (candidate source out : List Bool) (cp sp kept cap count logCap : Nat) (eq found : Bool) :
    step boot (cfg 0 candidate source out cp sp kept cap count logCap eq found)=
      some (cfg 1 candidate source out cp sp kept cap count logCap eq false) := by
  simp [step,boot,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,writeTapeBit]

theorem input_eq (candidate source out : List Bool) (cp sp kept cap count logCap : Nat) (eq found : Bool) :
    TapeEmbedding.config ![out.length,kept+1] ![out,CompareMachine.word kept]
      (PhysicalParityRestore.input candidate source cp sp eq found cap count logCap)=
      cfg scan.start candidate source out cp sp kept cap count logCap eq found := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;>
      simp [cfg,PhysicalParityRestore.input,ZeroPadding.config,Rewind.recording,Rewind.config,
        PhysicalParityScan.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,PhysicalParityReuse.cfg,Fin.addCases]
  · funext i; fin_cases i <;>
      simp [cfg,PhysicalParityRestore.input,ZeroPadding.config,Rewind.recording,Rewind.config,
        PhysicalParityScan.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,PhysicalParityReuse.cfg,
        Rewind.Workspace.capacities,ZeroPadding.pad,Fin.addCases]

noncomputable def scanFinal : Fin scanSize := (1 : Fin 2).natAdd (scanSize-2)

theorem ending_eq (candidate source out : List Bool) (cp sp kept cap count logCap : Nat) (eq found : Bool) :
    TapeEmbedding.config ![out.length,kept+1] ![out,CompareMachine.word kept]
      (PhysicalParityRestore.ending candidate source cp sp eq found cap count logCap)=
      cfg scanFinal candidate source out cp sp kept cap count logCap eq found := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;>
      simp [cfg,PhysicalParityRestore.ending,SelectiveReset.finished,Rewind.config,
        PhysicalParityScan.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,PhysicalParityReuse.cfg,Fin.addCases]
  · funext i; fin_cases i <;>
      simp [cfg,PhysicalParityRestore.ending,SelectiveReset.finished,Rewind.config,
        PhysicalParityScan.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,PhysicalParityReuse.cfg,Fin.addCases]

theorem focus_eq (q : Fin 6) (candidate source out : List Bool)
    (cp sp kept cap count logCap : Nat) (eq found : Bool) :
    RecoveryFocus.config slots
      (cfg q candidate source out cp sp kept cap count logCap eq found).heads
      (cfg q candidate source out cp sp kept cap count logCap eq found).tapes
      (MaskSelect.cfg q candidate cp out kept found)=
      cfg q candidate source out cp sp kept cap count logCap eq found := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,pick_slots,cfg,MaskSelect.cfg]
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,pick_slots,cfg,MaskSelect.cfg]

theorem focus_changed (q : Fin 6) (candidate source out nextOut : List Bool)
    (cp nextCp sp kept nextKept cap count logCap : Nat) (eq found : Bool) :
    RecoveryFocus.config slots
      (cfg q candidate source out cp sp kept cap count logCap eq found).heads
      (cfg q candidate source out cp sp kept cap count logCap eq found).tapes
      (MaskSelect.cfg q candidate nextCp nextOut nextKept found)=
      cfg q candidate source nextOut nextCp sp nextKept cap count logCap eq found := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,pick_slots,cfg,MaskSelect.cfg]
  · funext i; fin_cases i <;> simp [RecoveryFocus.config,pick_slots,cfg,MaskSelect.cfg]

def coefficient (bits : List Bool) (rows : List PhysicalParityScan.Clause) : Bool :=
  PhysicalCoefficientAlgebra.coefficient (PhysicalParityScan.supportRecord bits) rows

def budget (B count cap : Nat) := 2*(count*(2*cap+5)+3)+2+(2*B+4)+3

theorem support_stream (bits : List Bool) :
    ClauseEquality.stream (PhysicalParityScan.supportRecord bits)=frame bits++[false,false] := by
  simp [ClauseEquality.stream,PhysicalParityScan.supportRecord,frame,List.append_assoc]

theorem scan_run (bits candidatePrefix sourcePrefix candidateSuffix sourceSuffix out : List Bool)
    (rows : List PhysicalParityScan.Clause) (kept cap logCap : Nat) (eq : Bool)
    (hcap : ∀ row∈rows,PhysicalParityProbe.budget (PhysicalParityScan.supportRecord bits) row≤cap)
    (hlog : rows.length*(2*cap+5)+3≤logCap) :
    ∃ r,runFrom scan (2*(rows.length*(2*cap+5)+3)+2)
      (cfg scan.start (candidatePrefix++frame bits++[false,false]++candidateSuffix)
        (sourcePrefix++PhysicalParityScan.stream rows++sourceSuffix) out
        candidatePrefix.length sourcePrefix.length kept cap rows.length logCap eq false)=some r ∧
      r.steps≤2*(rows.length*(2*cap+5)+3)+2 ∧
      r.final=cfg scanFinal (candidatePrefix++frame bits++[false,false]++candidateSuffix)
        (sourcePrefix++PhysicalParityScan.stream rows++sourceSuffix) out
        candidatePrefix.length sourcePrefix.length kept cap rows.length logCap
        (PhysicalParityScan.endEq (PhysicalParityScan.supportRecord bits) rows eq) (coefficient bits rows) := by
  obtain ⟨r,hr,hs,hf⟩ := PhysicalParityRestore.ready_run_suffix (PhysicalParityScan.supportRecord bits)
    candidatePrefix sourcePrefix rows sourceSuffix candidateSuffix eq false cap logCap hcap hlog
  have he := TapeEmbedding.run_embed PhysicalParityRestore.machine ![out.length,kept+1]
    ![out,CompareMachine.word kept] _ _ r hr
  rw [input_eq] at he
  refine ⟨TapeEmbedding.receipt ![out.length,kept+1] ![out,CompareMachine.word kept] r,?_,hs,?_⟩
  · simpa only [scan,support_stream,List.append_assoc] using he
  · change TapeEmbedding.config _ _ r.final=_
    rw [hf,ending_eq]
    simp only [coefficient,support_stream,List.append_assoc]

theorem emit_run (bits pre suffix source out : List Bool) (sp kept cap count logCap : Nat) (eq found : Bool) :
    ∃ r,runFrom emit (2*bits.length+4)
      (cfg emit.start (pre++frame bits++[false,false]++suffix) source out pre.length sp kept cap count logCap eq found)=some r ∧
      r.steps=2*bits.length+4 ∧
      r.final=cfg 5 (pre++frame bits++[false,false]++suffix) source (out++MaskSelect.output found bits)
        (pre.length+(frame bits).length+2) sp (kept+found.toNat) cap count logCap eq found := by
  obtain ⟨r,hr,hf,hs⟩ := MaskSelect.select_run bits pre suffix out kept found
  let ambient := cfg (0 : Fin 6) (pre++frame bits++[false,false]++suffix) source out pre.length sp kept cap count logCap eq found
  obtain ⟨result,he,hef,hes⟩ := RecoveryFocus.run_config slots slots_injective MaskSelect.machine
    ambient.heads ambient.tapes _ _ r hr
  rw [focus_eq] at he
  refine ⟨result,he,hes.trans hs,?_⟩
  rw [hef,hf]
  exact focus_changed 5 _ _ _ _ _ _ _ _ _ _ _ _ _ _

noncomputable def finalCode : Fin size := ((5 : Fin 6).natAdd scanSize).natAdd 2

theorem body_run (bits candidatePrefix sourcePrefix candidateSuffix sourceSuffix out : List Bool)
    (rows : List PhysicalParityScan.Clause) (kept cap logCap : Nat) (eq found : Bool)
    (hcap : ∀ row∈rows,PhysicalParityProbe.budget (PhysicalParityScan.supportRecord bits) row≤cap)
    (hlog : rows.length*(2*cap+5)+3≤logCap) :
    ∃ r,runFrom body (budget bits.length rows.length cap)
      (cfg body.start (candidatePrefix++frame bits++[false,false]++candidateSuffix)
        (sourcePrefix++PhysicalParityScan.stream rows++sourceSuffix) out
        candidatePrefix.length sourcePrefix.length kept cap rows.length logCap eq found)=some r ∧
      r.steps≤budget bits.length rows.length cap ∧
      r.final=cfg finalCode (candidatePrefix++frame bits++[false,false]++candidateSuffix)
        (sourcePrefix++PhysicalParityScan.stream rows++sourceSuffix) (out++MaskSelect.output (coefficient bits rows) bits)
        (candidatePrefix.length+(frame bits).length+2) sourcePrefix.length (kept+(coefficient bits rows).toNat)
        cap rows.length logCap (PhysicalParityScan.endEq (PhysicalParityScan.supportRecord bits) rows eq)
        (coefficient bits rows) := by
  obtain ⟨a,ha,has,haf⟩ := scan_run bits candidatePrefix sourcePrefix candidateSuffix sourceSuffix out rows kept cap logCap eq hcap hlog
  obtain ⟨b,hb,hbs,hbf⟩ := emit_run bits candidatePrefix candidateSuffix
    (sourcePrefix++PhysicalParityScan.stream rows++sourceSuffix) out sourcePrefix.length kept cap rows.length logCap
    (PhysicalParityScan.endEq (PhysicalParityScan.supportRecord bits) rows eq) (coefficient bits rows)
  have hb' : runFrom emit (2*bits.length+4) (Composition.restart a.final emit.start)=some b := by rw [haf]; exact hb
  have ab := Composition.run_join scan emit _ _ _ a b ha hb'
  obtain ⟨c,hc,hcf,hcs⟩ := (Timed.single (by rfl) (boot_step
    (candidatePrefix++frame bits++[false,false]++candidateSuffix)
    (sourcePrefix++PhysicalParityScan.stream rows++sourceSuffix) out
    candidatePrefix.length sourcePrefix.length kept cap rows.length logCap eq found)).run (by rfl)
  have hab : runFrom tail ((2*(rows.length*(2*cap+5)+3)+2)+1+(2*bits.length+4))
      (Composition.restart c.final tail.start)=some (Composition.joinedReceipt a b) := by
    rw [hcf]
    exact ab
  have h := Composition.run_join boot tail _ _ _ c (Composition.joinedReceipt a b) hc hab
  have ht : 1+1+(2*(rows.length*(2*cap+5)+3)+2+1+(2*bits.length+4))=budget bits.length rows.length cap := by
    unfold budget; omega
  rw [ht] at h
  refine ⟨_,h,?_,?_⟩
  · simp only [Composition.joinedReceipt,hcs,hbs]; unfold budget; omega
  · change Composition.rightConfig 2 (Composition.rightConfig scanSize b.final)=_
    rw [hbf]
    rfl

end PCJ9eff70d512234a4c_Fixed.Materializer.ParityFilter

import Proof.Packets.ParityFilterBody

/-! An ordinary counted loop filters a resident candidate bank by coefficients
computed from the original raw polynomial. Both counts are actual unary tapes. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ParityFilter
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding

def candidateStream (masks : List (List Bool)) :=
  PhysicalParityScan.stream (masks.map PhysicalParityScan.supportRecord)
@[simp] theorem candidateStream_nil : candidateStream []=[] := rfl
@[simp] theorem candidateStream_cons (bits : List Bool) (rows : List (List Bool)) :
    candidateStream (bits::rows)=frame bits++[false,false]++candidateStream rows := by
  simp only [candidateStream,List.map_cons,PhysicalParityScan.stream_cons,support_stream]

def selected (rows : List PhysicalParityScan.Clause) (masks : List (List Bool)) :=
  masks.filter (fun bits => coefficient bits rows)
noncomputable def flags (rows : List PhysicalParityScan.Clause) : List (List Bool) → Bool → Bool → Bool×Bool
  | [],eq,found => (eq,found)
  | bits::masks,eq,_ => flags rows masks
      (PhysicalParityScan.endEq (PhysicalParityScan.supportRecord bits) rows eq) (coefficient bits rows)

noncomputable def machine := RepeatMachine.machine body (fun _ _=>true)
noncomputable def loopCfg (phase : Fin 5) (candidate source out : List Bool)
    (cp sp kept cap count logCap total driver : Nat) (eq found : Bool) :=
  RepeatMachine.cfg phase (cfg body.start candidate source out cp sp kept cap count logCap eq found) total driver

theorem body_control (q : Fin size) (phase : Fin 5) (candidate source out : List Bool)
    (cp sp kept cap count logCap total driver : Nat) (eq found : Bool) :
    RepeatMachine.cfg phase (cfg q candidate source out cp sp kept cap count logCap eq found) total driver=
      loopCfg phase candidate source out cp sp kept cap count logCap total driver eq found := rfl

theorem output_cons (rows : List PhysicalParityScan.Clause) (bits : List Bool) (masks : List (List Bool)) :
    MaskSelect.output (coefficient bits rows) bits++(selected rows masks).flatten=
      (selected rows (bits::masks)).flatten := by
  cases h : coefficient bits rows <;> simp [selected,MaskSelect.output,h]

theorem count_cons (rows : List PhysicalParityScan.Clause) (bits : List Bool) (masks : List (List Bool)) :
    (coefficient bits rows).toNat+(selected rows masks).length=(selected rows (bits::masks)).length := by
  cases h : coefficient bits rows <;> simp [selected,h,Nat.add_comm]

theorem filter_remaining (B : Nat) (masks : List (List Bool))
    (candidatePrefix sourcePrefix candidateSuffix sourceSuffix out : List Bool)
    (rows : List PhysicalParityScan.Clause) (kept cap logCap total pos : Nat) (eq found : Bool)
    (hn : pos+masks.length=total)
    (hw : ∀ bits∈masks,bits.length=B)
    (hcap : ∀ bits∈masks,∀ row∈rows,PhysicalParityProbe.budget (PhysicalParityScan.supportRecord bits) row≤cap)
    (hlog : rows.length*(2*cap+5)+3≤logCap) :
    ∃ r,runFrom machine (masks.length*(budget B rows.length cap+2)+total+3)
      (loopCfg 0 (candidatePrefix++candidateStream masks++candidateSuffix)
        (sourcePrefix++PhysicalParityScan.stream rows++sourceSuffix) out
        candidatePrefix.length sourcePrefix.length kept cap rows.length logCap total (pos+1) eq found)=some r ∧
      r.steps≤ masks.length*(budget B rows.length cap+2)+total+3 ∧
      r.final=loopCfg 3 (candidatePrefix++candidateStream masks++candidateSuffix)
        (sourcePrefix++PhysicalParityScan.stream rows++sourceSuffix) (out++(selected rows masks).flatten)
        (candidatePrefix.length+(candidateStream masks).length) sourcePrefix.length
        (kept+(selected rows masks).length) cap rows.length logCap total 1
        (flags rows masks eq found).1 (flags rows masks eq found).2 := by
  induction masks generalizing candidatePrefix out kept pos eq found with
  | nil =>
    have hp : pos=total := by simpa using hn
    subst pos
    obtain ⟨r,hr,hf,hs⟩ := (RepeatMachine.exhaust body (fun _ _=>true)
      (cfg body.start (candidatePrefix++candidateSuffix)
        (sourcePrefix++PhysicalParityScan.stream rows++sourceSuffix) out
        candidatePrefix.length sourcePrefix.length kept cap rows.length logCap eq found) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,?_,?_,?_⟩
    · simpa [machine,loopCfg] using hr
    · simpa using hs.le
    · simpa [loopCfg,selected,flags] using hf
  | cons bits masks ih =>
    have hb := hw bits (by simp)
    obtain ⟨first,hfirst,hfirsts,hfirstf⟩ := body_run bits candidatePrefix sourcePrefix
      (candidateStream masks++candidateSuffix) sourceSuffix out rows kept cap logCap eq found (hcap bits (by simp)) hlog
    rw [hb] at hfirst hfirsts
    have it := RepeatMachine.iteration body (fun _ _=>true)
      (cfg body.start (candidatePrefix++frame bits++[false,false]++(candidateStream masks++candidateSuffix))
        (sourcePrefix++PhysicalParityScan.stream rows++sourceSuffix) out
        candidatePrefix.length sourcePrefix.length kept cap rows.length logCap eq found)
      total pos first rfl (by simp only [List.length_cons] at hn; omega) hfirst
    rw [hfirstf,body_control,body_control] at it
    simp only [ite_true] at it
    obtain ⟨rest,hrest,hrests,hrestf⟩ := ih (candidatePrefix++frame bits++[false,false])
      (out++MaskSelect.output (coefficient bits rows) bits) (kept+(coefficient bits rows).toNat) (pos+1)
      (PhysicalParityScan.endEq (PhysicalParityScan.supportRecord bits) rows eq) (coefficient bits rows)
      (by simp only [List.length_cons] at hn; omega)
      (fun x hx=>hw x (by simp [hx])) (fun x hx=>hcap x (by simp [hx]))
    have hm : loopCfg 0 (candidatePrefix++frame bits++[false,false]++(candidateStream masks++candidateSuffix))
        (sourcePrefix++PhysicalParityScan.stream rows++sourceSuffix) (out++MaskSelect.output (coefficient bits rows) bits)
        (candidatePrefix.length+(frame bits).length+2) sourcePrefix.length
        (kept+(coefficient bits rows).toNat) cap rows.length logCap total (pos+2)
        (PhysicalParityScan.endEq (PhysicalParityScan.supportRecord bits) rows eq) (coefficient bits rows)=
      loopCfg 0 ((candidatePrefix++frame bits++[false,false])++candidateStream masks++candidateSuffix)
        (sourcePrefix++PhysicalParityScan.stream rows++sourceSuffix) (out++MaskSelect.output (coefficient bits rows) bits)
        (candidatePrefix++frame bits++[false,false]).length sourcePrefix.length
        (kept+(coefficient bits rows).toNat) cap rows.length logCap total ((pos+1)+1)
        (PhysicalParityScan.endEq (PhysicalParityScan.supportRecord bits) rows eq) (coefficient bits rows) := by
      simp only [List.append_assoc,List.length_append,List.length_cons,List.length_nil,Nat.add_assoc]
    rw [hm] at it
    rcases it with ⟨space,it⟩
    obtain ⟨result,hr,hf,hs,_⟩ := it.followedBy rest hrest
    have htime : (first.steps+2)+(masks.length*(budget B rows.length cap+2)+total+3)≤
        (bits::masks).length*(budget B rows.length cap+2)+total+3 := by
      simp only [List.length_cons]; nlinarith
    have more := runFrom_moreFuel machine _
      ((bits::masks).length*(budget B rows.length cap+2)+total+3-
        ((first.steps+2)+(masks.length*(budget B rows.length cap+2)+total+3))) _ result hr
    rw [Nat.add_sub_of_le htime] at more
    refine ⟨result,?_,?_,?_⟩
    · simpa only [candidateStream_cons,List.append_assoc] using more
    · rw [hs]; omega
    · rw [hf,hrestf]
      simp only [candidateStream_cons,flags,List.length_append,List.length_cons,List.length_nil,
        List.append_assoc,Nat.add_assoc,output_cons,count_cons]

theorem filter_run (B : Nat) (masks : List (List Bool))
    (candidatePrefix sourcePrefix candidateSuffix sourceSuffix out : List Bool)
    (rows : List PhysicalParityScan.Clause) (kept cap logCap : Nat) (eq found : Bool)
    (hw : ∀ bits∈masks,bits.length=B)
    (hcap : ∀ bits∈masks,∀ row∈rows,PhysicalParityProbe.budget (PhysicalParityScan.supportRecord bits) row≤cap)
    (hlog : rows.length*(2*cap+5)+3≤logCap) :
    ∃ r,runFrom machine (masks.length*(budget B rows.length cap+3)+3)
      (loopCfg 0 (candidatePrefix++candidateStream masks++candidateSuffix)
        (sourcePrefix++PhysicalParityScan.stream rows++sourceSuffix) out
        candidatePrefix.length sourcePrefix.length kept cap rows.length logCap masks.length 1 eq found)=some r ∧
      r.steps≤ masks.length*(budget B rows.length cap+3)+3 ∧
      r.final=loopCfg 3 (candidatePrefix++candidateStream masks++candidateSuffix)
        (sourcePrefix++PhysicalParityScan.stream rows++sourceSuffix) (out++(selected rows masks).flatten)
        (candidatePrefix.length+(candidateStream masks).length) sourcePrefix.length
        (kept+(selected rows masks).length) cap rows.length logCap masks.length 1
        (flags rows masks eq found).1 (flags rows masks eq found).2 := by
  have h := filter_remaining B masks candidatePrefix sourcePrefix candidateSuffix sourceSuffix out rows
    kept cap logCap masks.length 0 eq found (by omega) hw hcap hlog
  have ht : masks.length*(budget B rows.length cap+2)+masks.length+3=
      masks.length*(budget B rows.length cap+3)+3 := by ring
  simpa only [ht,Nat.zero_add] using h

end PCJ9eff70d512234a4c_Fixed.Materializer.ParityFilter

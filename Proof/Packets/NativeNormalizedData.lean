import Proof.Packets.NativeMaskCount
import Proof.Packets.NormalizedAddition

/-! A native monomial stream is physically parsed into raw support masks,
counted, and returned to the ready operand layout. The source polynomial
and its row count are not supplied a second time as mask-bank advice. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativeNormalized
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryExecution

def masks (C : Nat) (P : List (List Nat)) := P.map (ExtIncidence.maskOf C)
def extra (C : Nat) (P : List (List Nat)) : Fin 2→List Bool :=
  ![ExtIncidence.stream P,List.replicate C false]
def H (sourcePos outputPos countPos : Nat) (i : Fin 32) : Nat :=
  if i=26 then outputPos else if i=27 then countPos else
    Fin.addCases (m:=30) (n:=2) (motive:=fun _=>Nat) NormalizedAddition.heads (![sourcePos,0] : Fin 2→Nat) i
def A (C : Nat) (P : List (List Nat)) (raw : List (List Bool)) : Fin 32→List Bool :=
  Fin.addCases (m:=30) (n:=2) (motive:=fun _=>List Bool)
    (NormalizedAddition.data C [] raw []) (extra C P)
def nativeSlots : Fin 5→Fin 32 := ![30,24,31,26,27]
def countSlots : Fin 1→Fin 32 := ![27]
def backSlots : Fin 4→Fin 32 := ![24,26,29,27]
noncomputable abbrev native := RecoveryFocus.machine nativeSlots NativeMaskCount.machine
noncomputable abbrev countReady := RecoveryFocus.machine countSlots PairCountReady.machine
noncomputable abbrev back := RecoveryFocus.machine backSlots MaskBack.machine
noncomputable abbrev prepare := Composition.machine native (Composition.machine countReady back)
def prepareBudget (C : Nat) (P : List (List Nat)) :=
  ExtIncidence.cost C P+1+(P.length+2+1+(P.length*(2*C+5)+3))

theorem masks_width (C : Nat) (P : List (List Nat)) : ∀m∈masks C P,m.length=C := by
  intro m hm
  obtain ⟨n,_,rfl⟩:=List.mem_map.mp hm
  exact ExtIncidence.maskOf_length C n

theorem native_step (C : Nat) (P : List (List Nat)) (hp : ∀m∈P,∀code∈m,code<C) :
    Step native (ExtIncidence.cost C P)
      (H 0 0 1) (A C P [])
      (H (ExtIncidence.stream P).length (masks C P).flatten.length (P.length+1)) (A C P (masks C P)) := by
  obtain ⟨r,rr,rf,_⟩:=NativeMaskCount.stream_run [] [] C P hp [] 0
  have rs:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  refine PhysicalFocusBoundary.focus rs nativeSlots (by decide)
    (H 0 0 1) (H (ExtIncidence.stream P).length (masks C P).flatten.length (P.length+1))
    (A C P []) (A C P (masks C P)) ?_ ?_ ?_ ?_ ?_
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> simp [A,extra,nativeSlots,Fin.addCases,
      NativeMaskCount.cfg,NormalizedAddition.data,NormalizedAddition.extras,CompareMachine.word]
  · intro i;fin_cases i <;> simp [NormalizedAddition.heads,NormalizedAddition.extraHeads,H,nativeSlots,NativeMaskCount.cfg,Fin.addCases,masks,ExtIncidence.table]
  · intro i;fin_cases i <;> simp [A,extra,nativeSlots,Fin.addCases,NativeMaskCount.cfg,
      NormalizedAddition.data,NormalizedAddition.extras,CompareMachine.word,masks,ExtIncidence.table]
  · intro i away
    fin_cases i
    all_goals first | exact ⟨rfl,rfl⟩ | exact False.elim (away 0 rfl) |
      exact False.elim (away 3 rfl) | exact False.elim (away 4 rfl)

theorem count_step (C : Nat) (P : List (List Nat)) :
    Step countReady (P.length+2)
      (H (ExtIncidence.stream P).length (masks C P).flatten.length (P.length+1)) (A C P (masks C P))
      (H (ExtIncidence.stream P).length (masks C P).flatten.length 1) (A C P (masks C P)) := by
  obtain ⟨r,rr,rf,_⟩:=PairCountReady.run P.length
  have rs:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  refine PhysicalFocusBoundary.focus rs countSlots (by decide) _ _ _ _ ?_ ?_ ?_ ?_ ?_
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;simp [A,countSlots,Fin.addCases,NormalizedAddition.data,
      NormalizedAddition.extras,PairCountReady.cfg,masks]
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;simp [A,countSlots,Fin.addCases,NormalizedAddition.data,
      NormalizedAddition.extras,PairCountReady.cfg,masks]
  · intro i away
    have hi : i≠27 := by intro he;subst i;exact away 0 rfl
    exact ⟨by simp [H,hi],rfl⟩

theorem back_step (C : Nat) (P : List (List Nat)) :
    Step back (P.length*(2*C+5)+3)
      (H (ExtIncidence.stream P).length (masks C P).flatten.length 1) (A C P (masks C P))
      (H (ExtIncidence.stream P).length 0 1) (A C P (masks C P)) := by
  have hf : (masks C P).flatten.length=P.length*C := ExtIncidence.table_length C P
  obtain ⟨r,rr,rf,_⟩:=MaskBack.back_run C P.length 0 (masks C P).flatten []
  have rs:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  refine PhysicalFocusBoundary.focus rs backSlots (by decide) _ _ _ _ ?_ ?_ ?_ ?_ ?_
  · intro i;fin_cases i <;> simp [NormalizedAddition.heads,NormalizedAddition.extraHeads,H,backSlots,MaskBack.loopCfg,MaskBack.cfg,MaskSeek.cfg,
      Fin.addCases,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hf]
  · intro i;fin_cases i <;> simp [A,backSlots,MaskBack.loopCfg,MaskBack.cfg,MaskSeek.cfg,
      Fin.addCases,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
      NormalizedAddition.data,NormalizedAddition.extras,masks]
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> simp [A,backSlots,MaskBack.loopCfg,MaskBack.cfg,MaskSeek.cfg,
      Fin.addCases,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
      NormalizedAddition.data,NormalizedAddition.extras,masks]
  · intro i away
    have hi : i≠26 := by intro he;subst i;exact away 1 rfl
    exact ⟨by simp [H,hi],rfl⟩

theorem prepare_step (C : Nat) (P : List (List Nat)) (hp : ∀m∈P,∀code∈m,code<C) :
    Step prepare (prepareBudget C P) (H 0 0 1) (A C P [])
      (H (ExtIncidence.stream P).length 0 1) (A C P (masks C P)) :=
  (native_step C P hp).seq ((count_step C P).seq (back_step C P))

end PCJ9eff70d512234a4c_Fixed.Materializer.NativeNormalized

import Proof.Packets.PacketsXWalkTranscriptRewindJoined

/-! The initial walk arena is built by physical fanout from fifteen retained
palette words and empty destination tapes. Its population counter is incremented
for the forthcoming transcript allocation. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralCold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open VectorBottomUp CloseoutRowsModeCache
noncomputable section

def select (i : Fin 299) : Option (Fin 15) :=
  if i=31 then some 2 else if i=297 then some 14 else none

def work (R S N : Nat) (i : Fin 299) : List Bool :=
  if i=31 then ZeroPadding.pad S (UnaryTemplate.tape R) else
  if i=297 then ZeroPadding.pad S (CompareMachine.word N) else List.replicate S false

def boot := Composition.machine (NativeFanout.machine select) paletteRaise

theorem work_ready (R S N : Nat) : TranscriptRewindReady R S N (work R S N) := by
  constructor <;> simp [work]

theorem work_length (R S N : Nat) (hR : R+2≤S) (hN : N+1≤S) :
    ∀i,(work R S N i).length≤S := by
  intro i
  by_cases hi : i=31
  · simp [work,hi,ZeroPadding.pad_length,UnaryTemplate.tape];omega
  by_cases hj : i=297
  · simp [work,hi,hj,ZeroPadding.pad_length,CompareMachine.word];omega
  · simp [work,hi,hj]

theorem work_update (R S N : Nat) :
    Function.update (work R S N) 297 (ZeroPadding.pad S (CompareMachine.word (N+1)))=work R S (N+1) := by
  funext i
  by_cases hi : i=297
  · subst i;simp [work]
  · simp [work,Function.update_of_ne hi,hi]

theorem boot_run (C R M root depth S : Nat) (p : Parameters)
    (h : ColdWordBounds C R M root depth p) (hRS : R+3≤S) (hCS : 2*C+5≤S) :
    Step boot (2*S+6) (fun _=>0)
      (NativeFanout.input (m:=299) (paddedPalette C R M root depth p) S)
      (paletteHeads VectorNumericArena.heads)
      (paletteData (paddedPalette C R M root depth p) S (work R S M)) := by
  have hlen : ∀i,(paddedPalette C R M root depth p i).length≤S := by
    intro i
    have hi:=cold_palette_length C R M root depth S p h hRS hCS i
    simp only [paddedPalette,ZeroPadding.pad_length]
    exact max_le (by omega) hi
  have first:=Step.of_ready (NativeFanout.ready select (paddedPalette C R M root depth p) S hlen)
  have routed : (fun i=>ZeroPadding.pad S (NativeFanout.word select (paddedPalette C R M root depth p) i))=
      work R S M := by
    funext i
    have hrs : R≤S := by omega
    by_cases h31 : i=31
    · subst i;simp [NativeFanout.word,select,work,paddedPalette,coldPalette,
        MatrixBucketRootPower.pad_pad R S _ hrs]
    by_cases h297 : i=297
    · subst i;simp [NativeFanout.word,select,work,paddedPalette,coldPalette,
        MatrixBucketRootPower.pad_pad R S _ hrs]
    · simp [NativeFanout.word,select,work,h31,h297,ZeroPadding.pad]
  have output : NativeFanout.output select (paddedPalette C R M root depth p) S=
      paletteData (paddedPalette C R M root depth p) S (work R S M) := by
    change paletteData (paddedPalette C R M root depth p) S
      (fun i=>ZeroPadding.pad S (NativeFanout.word select (paddedPalette C R M root depth p) i))=_
    rw [routed]
  rw [output] at first
  have joined:=first.seq (palette_raise_run _)
  simpa only [boot,show 2*S+4+1+1=2*S+6 by omega] using joined

def increment := RecoveryFocus.machine (fun _ : Fin 1=>(312 : Fin 316)) VectorCounter.increment

theorem increment_run (R S M : Nat) (palette : Fin 15→List Bool) :
    Step increment (2*M+2) (paletteHeads VectorNumericArena.heads) (paletteData palette S (work R S M))
      (paletteHeads VectorNumericArena.heads) (paletteData palette S (work R S (M+1))) := by
  have step:=VectorCounter.increment_padded M S
  apply PhysicalFocusBoundary.focus step (fun _ : Fin 1=>(312 : Fin 316)) (by intro i j _;exact Subsingleton.elim i j)
    (paletteHeads VectorNumericArena.heads) (paletteHeads VectorNumericArena.heads)
    (paletteData palette S (work R S M)) (paletteData palette S (work R S (M+1)))
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;simp [paletteData,work,Fin.addCases]
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;simp [paletteData,work,Fin.addCases]
  · intro i away
    refine ⟨rfl,?_⟩
    have hi : i≠312 := by intro he;exact away 0 he.symm
    have eqn:=palette_update_work palette S (work R S M) 297 (ZeroPadding.pad S (CompareMachine.word (M+1)))
    rw [work_update] at eqn
    have he:=congrFun eqn i
    simpa only [show paletteArenaSlots 297=(312 : Fin 316) from rfl,Function.update_of_ne hi] using he

def paletteMachine := Composition.machine boot increment
def paletteBudget (S M : Nat) := 2*S+2*M+9

theorem palette_run (C R M root depth S : Nat) (p : Parameters)
    (h : ColdWordBounds C R M root depth p) (hRS : R+3≤S) (hCS : 2*C+5≤S) :
    Step paletteMachine (paletteBudget S M) (fun _=>0)
      (NativeFanout.input (m:=299) (paddedPalette C R M root depth p) S)
      (paletteHeads VectorNumericArena.heads)
      (paletteData (paddedPalette C R M root depth p) S (work R S (M+1))) := by
  have joined:=(boot_run C R M root depth S p h hRS hCS).seq
    (increment_run R S M (paddedPalette C R M root depth p))
  simpa only [paletteMachine,paletteBudget,show 2*S+6+1+(2*M+2)=2*S+2*M+9 by omega] using joined

end
end Theorem25Completion.WalkLiteralCold

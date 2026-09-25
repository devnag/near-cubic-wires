import Proof.Rows.ClosureReusable48
import Proof.Rows.ClosureConstantGate

/-! Direct ordinary evaluation of one native strict threshold gate on one
physical assignment. The two signed scores and target adjustment are read
and computed, then compared; no table printer or ready gate answer is input. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.OffsetSourceGate
open LocalBitMultitape RepairOrdinary RecoveryRootRound RecoveryExecution ExtDecompositionBatch
open RepairRepresentation RepairSource RepairSource.CloseoutFinal RepairSource.VerifierDecoding
open CloseoutRowsPoolWeight SignedSortKey

def compareSlots : Fin 4→Fin 44 := ![13,14,21,22]
def frameSlots : Fin 3→Fin 44 := ![21,23,24]
def appendSlots : Fin 4→Fin 44 := ![23,25,26,34]
noncomputable def paired := Composition.machine C10NaturalHardwireScoreInputs.machine
  (TapeEmbedding.machine 23 C10NaturalHardwireTarget.pairMachine)
noncomputable def compare := RecoveryFocus.machine compareSlots compareMachine
noncomputable def invert := RecoveryFocus.machine frameSlots RecoveryLiteralSignFrame.machine
noncomputable def append := RecoveryFocus.machine appendSlots CloseoutRowsSignedAppend.sign
noncomputable def core := Composition.machine (Composition.machine (Composition.machine paired compare) invert) append
def budget (xs : List Item) (z : Int) (w C : Nat) :=
  C10NaturalHardwireScoreInputs.budget xs w C+C10NaturalHardwireTarget.pairBudget z w+4*w+18
def bit (xs : List Item) (z : Int) :=
  decide (z < (C10NaturalHardwireScore.selectedSum xs : Int)-CloseoutRowsPoolMinimum.liveSum xs)

private theorem zeros_pad (C n : Nat) (h : n ≤ C) :
    ZeroPadding.pad C (List.replicate n false)=List.replicate C false := by
  rw [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
  congr 1
  omega

private theorem compare_run (w C p n : Nat) (hc : 2*w+1 ≤ C)
    (hp : p < 2^w) (hn : n < 2^w) :
    Step compareMachine (4*w+4) (fun _=>0)
      ![MatrixScoreWeight.scalar C w n,MatrixScoreWeight.scalar C w p,
        List.replicate C false,List.replicate C false]
      (fun _=>0)
      ![MatrixScoreWeight.scalar C w n,MatrixScoreWeight.scalar C w p,
        ZeroPadding.pad C [decide (n≤p)],List.replicate C false] := by
  have h := (Step.of_ready (RecoveryRootRound.compare_ready (binary w n) (binary w p) C
    (by simp only [binary_length]))).pad (fun _=>C)
  simp only [binary_length,binary_value w n hn,binary_value w p hp,max_eq_left hc] at h
  refine (h.congr_in rfl ?_).congr rfl ?_
  all_goals
    funext i
    fin_cases i <;> first
      | rfl
      | exact zeros_pad C 1 (by omega)
      | exact (zeros_pad C 1 (by omega)).symm
      | exact (zeros_pad C C le_rfl).symm
      | exact zeros_pad C C le_rfl

private theorem heads_append (out next : List Bool) (pos mpos : Nat) :
    dockH appendSlots (C10NaturalHardwireScoreInputs.heads out pos mpos)
      ![0,0,0,next.length]=C10NaturalHardwireScoreInputs.heads next pos mpos := by
  funext i
  fin_cases i
  all_goals first
    | exact dockH_slot appendSlots (by decide) _ _ 0
    | exact dockH_slot appendSlots (by decide) _ _ 1
    | exact dockH_slot appendSlots (by decide) _ _ 2
    | exact dockH_slot appendSlots (by decide) _ _ 3
    | exact dockH_other appendSlots _ _ _ (by decide)

theorem core_run (xs : List Item) (z : Int) (tail mtail out : List Bool) (w C D : Nat)
    (hw : ∀ x∈xs, natBitLength x.1.natAbs ≤ w) (hc : 8*w+12 ≤ C)
    (hp : C10NaturalHardwireScore.positiveSum xs < 2^w)
    (hn : CloseoutRowsPoolMinimum.negSum xs < 2^w)
    (hD : C10NaturalHardwireScore.loopBudget xs w C ≤ D)
    (hz : natBitLength z.natAbs ≤ w)
    (hpz : C10NaturalHardwireTarget.pPart z (CloseoutRowsPoolMinimum.liveSum xs) < 2^w)
    (hnz : C10NaturalHardwireTarget.nPart z (C10NaturalHardwireScore.selectedSum xs) < 2^w) :
    ∃ result : Fin 44→List Bool,
      Step core (budget xs z w C) (C10NaturalHardwireScoreInputs.heads out 0 0)
        (C10NaturalHardwireScoreInputs.data (word xs++intWord z++tail) (mask xs++mtail)
          out w C D xs.length 0 0)
        (C10NaturalHardwireScoreInputs.heads (out++[bit xs z])
          ((word xs).length+(intWord z).length) xs.length) result ∧
      result 0=word xs++intWord z++tail ∧ result 34=out++[bit xs z] := by
  let source := word xs++intWord z++tail
  let membership := mask xs++mtail
  let pos := (word xs).length+(intWord z).length
  let p := C10NaturalHardwireTarget.pPart z (CloseoutRowsPoolMinimum.liveSum xs)
  let n := C10NaturalHardwireTarget.nPart z (C10NaturalHardwireScore.selectedSum xs)
  let flag := decide (n≤p)
  have first := C10NaturalHardwireScoreInputs.run xs (intWord z++tail) mtail out w C D hw hc hp hn hD
  rw [←List.append_assoc] at first
  obtain ⟨values,pairedRun,hsource,hpword,hnword⟩ := C10NaturalHardwireTarget.pair_run
    (word xs) tail z w C (C10NaturalHardwireScore.selectedSum xs)
      (CloseoutRowsPoolMinimum.liveSum xs) hz hc hpz hnz
  let extra := Fin.addCases (motive:=fun _=>List Bool) (C10NaturalHardwireTarget.extra C out)
    (C10NaturalHardwireScoreInputs.extra membership C D xs.length)
  let extraHeads : Fin 23→Nat := fun i=>if i=13 then out.length else if i=18 then xs.length
    else if i=21 then 1 else 0
  let A : Fin 44→List Bool := Fin.addCases (motive:=fun _=>List Bool) values extra
  have second : Step (TapeEmbedding.machine 23 C10NaturalHardwireTarget.pairMachine)
      (C10NaturalHardwireTarget.pairBudget z w)
      (C10NaturalHardwireScoreInputs.heads out (word xs).length xs.length)
      (C10NaturalHardwireScoreInputs.data source membership out w C D xs.length
        (C10NaturalHardwireScore.selectedSum xs) (CloseoutRowsPoolMinimum.liveSum xs))
      (C10NaturalHardwireScoreInputs.heads out pos xs.length) A := by
    have h := pairedRun.embed extraHeads extra
    refine (h.congr_in ?_ ?_).congr ?_ rfl
    all_goals funext i; fin_cases i <;>rfl
  have cmp := (compare_run w C p n (by omega) hpz hnz).dock compareSlots (by decide)
    (C10NaturalHardwireScoreInputs.heads out pos xs.length) A
    (by intro i;fin_cases i <;>rfl) (by
      intro i;fin_cases i
      · exact hnword
      · exact hpword
      all_goals rfl)
  let cmpWords : Fin 4→List Bool :=
    ![MatrixScoreWeight.scalar C w n,MatrixScoreWeight.scalar C w p,
      ZeroPadding.pad C [flag],List.replicate C false]
  let B := install compareSlots A cmpWords
  have compared : Step compare (4*w+4) (C10NaturalHardwireScoreInputs.heads out pos xs.length) A
      (C10NaturalHardwireScoreInputs.heads out pos xs.length) B :=
    cmp.congr (dockH_existing compareSlots _ _ (by intro i;fin_cases i <;>rfl)) rfl
  have framed : Step RecoveryLiteralSignFrame.machine 8 (fun _=>0)
      ![ZeroPadding.pad C [flag],List.replicate C false,List.replicate C false]
      (fun _=>0)
      ![ZeroPadding.pad C [flag],ZeroPadding.pad C (RepairOrdinary.frame [!flag]),
        List.replicate C false] := by
    have h := (CloseoutFinalSelector.step_of_clock (RecoveryLiteralSignFrame.sign_ready flag)).pad (fun _=>C)
    refine (h.congr_in rfl ?_).congr rfl ?_
    all_goals funext i;fin_cases i <;> first | rfl | exact zeros_pad C 3 (by omega)
  let frameWords : Fin 3→List Bool := ![ZeroPadding.pad C [flag],
    ZeroPadding.pad C (RepairOrdinary.frame [!flag]),List.replicate C false]
  let Z := install frameSlots B frameWords
  have inverted : Step invert 8 (C10NaturalHardwireScoreInputs.heads out pos xs.length) B
      (C10NaturalHardwireScoreInputs.heads out pos xs.length) Z := by
    have h := framed.dock frameSlots (by decide)
      (C10NaturalHardwireScoreInputs.heads out pos xs.length) B
      (by intro i;fin_cases i <;>rfl) (by
        intro i;fin_cases i
        · exact install_slot compareSlots (by decide) A cmpWords 2
        all_goals exact (install_other compareSlots A cmpWords _ (by decide)).trans rfl)
    exact h.congr (dockH_existing frameSlots _ _ (by intro i;fin_cases i <;>rfl)) rfl
  let framedFlag := ZeroPadding.pad C (RepairOrdinary.frame [!flag])
  let next := out++[!flag]
  have hread : readTapeBit framedFlag 1 = !flag := by
    rw [ZeroPadding.read_pad]
    rfl
  obtain ⟨ar,ha,haf,has⟩ := CloseoutRowsSignedAppend.sign_run framedFlag
    (List.replicate C false) (List.replicate C false) out
  have appendBit : Step CloseoutRowsSignedAppend.sign 2 ![0,0,0,out.length]
      ![framedFlag,List.replicate C false,List.replicate C false,out]
      ![0,0,0,next.length]
      ![framedFlag,List.replicate C false,List.replicate C false,next] := by
    refine ⟨ar,ha,?_,?_,has.le⟩
    all_goals rw [haf];simp only [CloseoutRowsSignedAppend.signResult,CloseoutRowsSignedAppend.signed,hread];rfl
  let appendWords : Fin 4→List Bool :=
    ![framedFlag,List.replicate C false,List.replicate C false,next]
  have appended := appendBit.dock appendSlots (by decide)
    (C10NaturalHardwireScoreInputs.heads out pos xs.length) Z
    (by intro i;fin_cases i <;>rfl) (by
      intro i;fin_cases i
      · exact install_slot frameSlots (by decide) B frameWords 1
      all_goals
        exact (install_other frameSlots B frameWords _ (by decide)).trans
          ((install_other compareSlots A cmpWords _ (by decide)).trans rfl))
  have finished := ((first.seq second).seq compared).seq inverted |>.seq appended
  have cost : (((C10NaturalHardwireScoreInputs.budget xs w C+1+
      C10NaturalHardwireTarget.pairBudget z w)+1+(4*w+4))+1+8)+1+2=budget xs z w C := by
    unfold budget
    omega
  rw [cost] at finished
  have hbit : (!flag) = bit xs z := by
    have hv := C10NaturalHardwireTarget.pair_value z
      (C10NaturalHardwireScore.selectedSum xs) (CloseoutRowsPoolMinimum.liveSum xs)
    have hle : n ≤ p ↔ (C10NaturalHardwireScore.selectedSum xs : Int)-
        CloseoutRowsPoolMinimum.liveSum xs ≤ z := by
      change (p : Int)-(n : Int)=_ at hv
      omega
    by_cases h : n ≤ p
    · have no : ¬ z < (C10NaturalHardwireScore.selectedSum xs : Int)-
          CloseoutRowsPoolMinimum.liveSum xs := by have h' := hle.mp h;omega
      simp [flag,bit,h,no]
    · have yes : z < (C10NaturalHardwireScore.selectedSum xs : Int)-
          CloseoutRowsPoolMinimum.liveSum xs := by
        have h' : ¬ (C10NaturalHardwireScore.selectedSum xs : Int)-
            CloseoutRowsPoolMinimum.liveSum xs ≤ z := fun ht=>h (hle.mpr ht)
        omega
      simp [flag,bit,h,yes]
  refine ⟨install appendSlots Z appendWords,finished.congr ?_ rfl,?_,?_⟩
  · rw [heads_append]
    change C10NaturalHardwireScoreInputs.heads (out++[!flag]) pos xs.length=_
    rw [hbit]
  · exact (install_other appendSlots Z appendWords 0 (by decide)).trans
      ((install_other frameSlots B frameWords 0 (by decide)).trans
        ((install_other compareSlots A cmpWords 0 (by decide)).trans hsource))
  · exact (install_slot appendSlots (by decide) Z appendWords 3).trans (by
      change out++[!flag]=out++[bit xs z]
      rw [hbit])

end NearCubicWires.P1Closure.OffsetSourceGate

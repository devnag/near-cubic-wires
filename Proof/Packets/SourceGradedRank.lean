import Proof.Packets.SourceClog
import Proof.Packets.UnaryMaximum
import Proof.Packets.UnaryAffine

/-! Actual canonical rank and depth from raw source population and actual
support/live touching count. All work tapes start empty. No logarithm, rank,
depth or max word is supplied at entry. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Completion.SourceGradedRank
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource NearCubicWires.RepairSource.VerifierDecoding

def affineSlots (i : Fin 11) : Fin 40:=i.castAdd 29
def maxSlots : Fin 4→Fin 40:=![9,11,12,13]
def depthSlots (i : Fin 12) : Fin 40:=if i=0 then 9 else ⟨i.val+13,by have :=i.isLt;omega⟩
def rankSlots (i : Fin 12) : Fin 40:=if i=0 then 12 else ⟨i.val+24,by have :=i.isLt;omega⟩
def rawRankSlots : Fin 3→Fin 40:=![34,36,37]
def rawDepthSlots : Fin 3→Fin 40:=![23,38,39]
theorem affine_inj:Function.Injective affineSlots:=by decide
theorem max_inj:Function.Injective maxSlots:=by decide
theorem depth_inj:Function.Injective depthSlots:=by decide
theorem rank_inj:Function.Injective rankSlots:=by decide
theorem rawRank_inj:Function.Injective rawRankSlots:=by decide
theorem rawDepth_inj:Function.Injective rawDepthSlots:=by decide

def input (population active : Nat) : Fin 40→List Bool:=
  fun i=>if i=0 then List.replicate active true else if i=11 then List.replicate population true else []
def depth (active : Nat):=Nat.clog 2 (256*active)
def rank (population active : Nat):=max (depth active) (Nat.clog 2 population)
noncomputable def machine:=Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine affineSlots (UnaryAffine.machine 256 0))
    (RecoveryFocus.machine maxSlots UnaryMaximum.machine))
    (RecoveryFocus.machine depthSlots SourceClog.machine))
    (RecoveryFocus.machine rankSlots SourceClog.machine))
    (RecoveryFocus.machine rawRankSlots (UWalkUnary.machine false false)))
    (RecoveryFocus.machine rawDepthSlots (UWalkUnary.machine false false))
def budget (population active : Nat):=
  ((((UnaryAffine.budget active 256 0+1+(2*max (256*active) population+4))+1+
    SourceClog.budget (256*active))+1+SourceClog.budget (max (256*active) population))+1+
    (2*rank population active+6)+1+(2*depth active+6))

theorem clog_max (n m : Nat):Nat.clog 2 (max n m)=max (Nat.clog 2 n) (Nat.clog 2 m):=by
  rcases le_total n m with h|h
  · rw [max_eq_right h,max_eq_right (Nat.clog_mono_right 2 h)]
  · rw [max_eq_left h,max_eq_left (Nat.clog_mono_right 2 h)]

private theorem no_affine (i : Fin 40) (h : 11 ≤ i.val):∀j,affineSlots j≠i:=by
  intro j he;have hv:=congrArg Fin.val he;have hj:=j.isLt
  simp only [affineSlots,Fin.val_castAdd] at hv;omega

/-- The populated outputs are raw rank36, Compare rank34, raw depth38,
Compare depth23. Original actual population11 and touching count0 survive. -/
theorem run (population active : Nat):∃O,
    Step machine (budget population active) (fun _=>0) (input population active) (fun _=>0) O ∧
    O 36=List.replicate (rank population active) true ∧
    O 34=CompareMachine.word (rank population active) ∧
    O 38=List.replicate (depth active) true ∧
    O 23=CompareMachine.word (depth active) ∧
    O 11=List.replicate population true ∧ O 0=List.replicate active true:=by
  obtain ⟨A,ha,a0,a9⟩:=UnaryAffine.run active 256 0
  have first:=SourceDock.dock ha affineSlots affine_inj (fun _=>0) (input population active)
    (by intro i;rfl) (by intro i;fin_cases i <;>rfl)
  have zh {k : Nat} (s:Fin k→Fin 40):dockH s (fun _=>0) (fun _=>0)=(fun _=>0):=
    SourceDock.heads_existing _ _ _ (by intro i;rfl)
  rw [zh] at first
  let A1:=install affineSlots (input population active) A
  have e1:A1=install affineSlots (input population active) A:=rfl
  have second:=SourceDock.dock (UnaryMaximum.run (256*active) population) maxSlots max_inj
    (fun _=>0) A1 (by intro i;rfl) (by
      intro i;fin_cases i
      · exact (install_slot affineSlots affine_inj _ A 9).trans (by simpa [UnaryMaximum.input] using a9)
      · rw [e1,install_other affineSlots _ _ _ (no_affine _ (by decide))];rfl
      · rw [e1,install_other affineSlots _ _ _ (no_affine _ (by decide))];rfl
      · rw [e1,install_other affineSlots _ _ _ (no_affine _ (by decide))];rfl)
  rw [zh] at second
  let A2:=install maxSlots A1 (UnaryMaximum.output (256*active) population)
  have e2:A2=install maxSlots A1 (UnaryMaximum.output (256*active) population):=rfl
  obtain ⟨D,hd,d10⟩:=SourceClog.run (256*active)
  have third:=SourceDock.dock hd depthSlots depth_inj (fun _=>0) A2
    (by intro i;rfl) (by
      intro i;fin_cases i
      · exact install_slot maxSlots max_inj _ _ 0
      all_goals rw [e2,install_other maxSlots _ _ _ (by decide),e1,
        install_other affineSlots _ _ _ (by decide)]
      all_goals rfl)
  rw [zh] at third
  let A3:=install depthSlots A2 D
  have e3:A3=install depthSlots A2 D:=rfl
  obtain ⟨T,ht,t10⟩:=SourceClog.run (max (256*active) population)
  have fourth:=SourceDock.dock ht rankSlots rank_inj (fun _=>0) A3
    (by intro i;rfl) (by
      intro i;fin_cases i
      · rw [e3,install_other depthSlots _ _ _ (by decide)]
        exact install_slot maxSlots max_inj _ _ 2
      all_goals rw [e3,install_other depthSlots _ _ _ (by decide),e2,
        install_other maxSlots _ _ _ (by decide),e1,install_other affineSlots _ _ _ (by decide)]
      all_goals rfl)
  rw [zh] at fourth
  let A4:=install rankSlots A3 T
  have e4:A4=install rankSlots A3 T:=rfl
  have tr:T 10=CompareMachine.word (rank population active):=by
    simpa only [clog_max,rank,depth] using t10
  have width:=UWalkUnary.ready false false 0 (rank population active)
  obtain ⟨wr,wrRun,wrT,wrH,wrS⟩:=width
  have wstep:Step (UWalkUnary.machine false false) (2*rank population active+6) (fun _=>0)
    (UWalkUnary.input 0 (rank population active)) (fun _=>0)
    (UWalkUnary.result false false 0 (rank population active)):=⟨wr,wrRun,funext wrH,wrT,wrS⟩
  have fifth:=SourceDock.dock wstep rawRankSlots rawRank_inj (fun _=>0) A4
    (by intro i;rfl) (by
      intro i;fin_cases i
      · change install rankSlots A3 T (rankSlots 10)=UWalkUnary.input 0 (rank population active) 0
        rw [install_slot rankSlots rank_inj]
        simpa [UWalkUnary.input,UWalkUnary.source] using tr
      all_goals rw [e4,install_other rankSlots _ _ _ (by decide),e3,install_other depthSlots _ _ _ (by decide),e2,install_other maxSlots _ _ _ (by decide),e1,install_other affineSlots _ _ _ (by decide)]
      all_goals rfl)
  rw [zh] at fifth
  let A5:=install rawRankSlots A4 (UWalkUnary.result false false 0 (rank population active))
  have e5:A5=install rawRankSlots A4 (UWalkUnary.result false false 0 (rank population active)):=rfl
  obtain ⟨dr,drRun,drT,drH,drS⟩:=UWalkUnary.ready false false 0 (depth active)
  have dstep:Step (UWalkUnary.machine false false) (2*depth active+6) (fun _=>0)
    (UWalkUnary.input 0 (depth active)) (fun _=>0)
    (UWalkUnary.result false false 0 (depth active)):=⟨dr,drRun,funext drH,drT,drS⟩
  have sixth:=SourceDock.dock dstep rawDepthSlots rawDepth_inj (fun _=>0) A5
    (by intro i;rfl) (by
      intro i;fin_cases i
      · rw [e5,install_other rawRankSlots _ _ _ (by decide),e4,install_other rankSlots _ _ _ (by decide)]
        change install depthSlots A2 D (depthSlots 10)=UWalkUnary.input 0 (depth active) 0
        rw [install_slot depthSlots depth_inj]
        simpa [UWalkUnary.input,UWalkUnary.source,depth] using d10
      all_goals rw [e5,install_other rawRankSlots _ _ _ (by decide),e4,install_other rankSlots _ _ _ (by decide),e3,install_other depthSlots _ _ _ (by decide),e2,install_other maxSlots _ _ _ (by decide),e1,install_other affineSlots _ _ _ (by decide)]
      all_goals rfl)
  rw [zh] at sixth
  refine ⟨_,((((first.seq second).seq third).seq fourth).seq fifth).seq sixth,?_,?_,?_,?_,?_,?_⟩
  · rw [install_other rawDepthSlots _ _ _ (by decide)]
    exact install_slot rawRankSlots rawRank_inj _ _ 1
  · rw [install_other rawDepthSlots _ _ _ (by decide)]
    change install rawRankSlots A4 (UWalkUnary.result false false 0 (rank population active)) (rawRankSlots 0)=_
    rw [install_slot rawRankSlots rawRank_inj]
    simp [UWalkUnary.result,UWalkUnary.source]
  · exact install_slot rawDepthSlots rawDepth_inj _ _ 1
  · change install rawDepthSlots A5 (UWalkUnary.result false false 0 (depth active)) (rawDepthSlots 0)=_
    rw [install_slot rawDepthSlots rawDepth_inj]
    simp [UWalkUnary.result,UWalkUnary.source]
  · rw [install_other rawDepthSlots _ _ _ (by decide),e5,install_other rawRankSlots _ _ _ (by decide),e4,install_other rankSlots _ _ _ (by decide),e3,install_other depthSlots _ _ _ (by decide)]
    exact install_slot maxSlots max_inj _ _ 1
  · rw [install_other rawDepthSlots _ _ _ (by decide),e5,install_other rawRankSlots _ _ _ (by decide),e4,install_other rankSlots _ _ _ (by decide),e3,install_other depthSlots _ _ _ (by decide),e2,install_other maxSlots _ _ _ (by decide)]
    exact (install_slot affineSlots affine_inj _ _ 0).trans a0

end Completion.SourceGradedRank

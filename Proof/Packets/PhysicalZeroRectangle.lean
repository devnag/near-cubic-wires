import Proof.Packets.PhysicalZeroBank

/-! Allocate an entire positive walk transcript from an empty tape using
only the physical packet-width, column-count and transition-count drivers. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalZeroRectangle
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open PhysicalZeroBank
noncomputable section

def rowFuel (R N : Nat) := N*(8*R+14)+3
def backFuel (R N : Nat) := N*(4*R+10)+7
def backRow := Composition.machine MaskBack.machine MaskBack.machine

theorem append_row (R N : Nat) (pre : List Bool) :
    Step PhysicalZeroBank.loop (rowFuel R N) (heads pre.length) (tapes R N pre)
      (heads (pre.length+N*(2*R))) (tapes R N (pre++List.replicate (N*(2*R)) false)) := by
  have body (i : Nat) (_ : i<N) : Step packet (8*R+11)
      (H (pre.length+i*(2*R))) (A R (pre++List.replicate (i*(2*R)) false))
      (H (pre.length+(i+1)*(2*R))) (A R (pre++List.replicate ((i+1)*(2*R)) false)) := by
    have h:=packet_run R (pre++List.replicate (i*(2*R)) false)
    have he : i*(2*R)+2*R=(i+1)*(2*R) := by ring
    simpa only [List.length_append,List.length_replicate,List.append_assoc,
      ←List.replicate_add,Nat.add_assoc,he] using h
  have h:=PhysicalRepeatStep.run packet N (8*R+11)
    (fun i=>H (pre.length+i*(2*R)))
    (fun i=>A R (pre++List.replicate (i*(2*R)) false)) body
  simp only [Nat.zero_mul,Nat.add_zero,List.replicate_zero,List.append_nil] at h
  convert h using 1
  all_goals first | rfl | (funext i;fin_cases i <;>rfl)

theorem back_row (R N pos : Nat) (bank : List Bool) :
    Step backRow (backFuel R N) (heads (pos+N*(2*R))) (tapes R N bank)
      (heads pos) (tapes R N bank) := by
  have first:=back_run R N (pos+N*R) bank
  have second:=back_run R N pos bank
  have he : pos+N*R+N*R=pos+N*(2*R) := by ring
  rw [he] at first
  have h:=first.seq second
  have fuel : N*(2*R+5)+3+1+(N*(2*R+5)+3)=backFuel R N := by unfold backFuel;ring
  simpa only [backRow,fuel] using h

def appendRows := Composition.machine (RepeatMachine.machine PhysicalZeroBank.loop (fun _ _=>true))
  (TapeEmbedding.machine 1 PhysicalZeroBank.loop)
def backRows := Composition.machine (RepeatMachine.machine backRow (fun _ _=>true))
  (TapeEmbedding.machine 1 backRow)
def machine := Composition.machine appendRows backRows
def H5 (pos : Nat) : Fin 5→Nat := Fin.addCases (m:=4) (n:=1) (motive:=fun _=>Nat) (heads pos) (fun _ : Fin 1=>1)
def A5 (R N n : Nat) (bank : List Bool) : Fin 5→List Bool :=
  Fin.addCases (m:=4) (n:=1) (motive:=fun _=>List Bool) (tapes R N bank) (fun _ : Fin 1=>CompareMachine.word n)
def appendFuel (R N n : Nat) := n*(rowFuel R N+3)+4+rowFuel R N
def rewindFuel (R N n : Nat) := n*(backFuel R N+3)+4+backFuel R N
def budget (R N n : Nat) := appendFuel R N n+1+rewindFuel R N n

attribute [local irreducible] PhysicalZeroBank.loop backRow

theorem append_rows (R N n : Nat) :
    Step appendRows (appendFuel R N n) (H5 0) (A5 R N n [])
      (H5 ((n+1)*(N*(2*R)))) (A5 R N n (List.replicate ((n+1)*(N*(2*R))) false)) := by
  let block:=N*(2*R)
  have localStep (i : Nat) (_ : i<n) : Step PhysicalZeroBank.loop (rowFuel R N)
      (heads (i*block)) (tapes R N (List.replicate (i*block) false))
      (heads ((i+1)*block)) (tapes R N (List.replicate ((i+1)*block) false)) := by
    have h:=append_row R N (List.replicate (i*block) false)
    have he : i*block+block=(i+1)*block := by ring
    simpa only [List.length_replicate,←List.replicate_add,show N*(2*R)=block from rfl,he] using h
  have first:=PhysicalRepeatStep.run PhysicalZeroBank.loop n (rowFuel R N)
    (fun i=>heads (i*block)) (fun i=>tapes R N (List.replicate (i*block) false)) localStep
  have last:=append_row R N (List.replicate (n*block) false)
  have he : n*block+block=(n+1)*block := by ring
  simp only [List.length_replicate,←List.replicate_add,show N*(2*R)=block from rfl,he] at last
  have finish:=last.embed (fun _ : Fin 1=>1) (fun _ : Fin 1=>CompareMachine.word n)
  have joined:=first.seq finish
  have fuel : n*(rowFuel R N+3)+3+1=n*(rowFuel R N+3)+4 := by omega
  simpa only [appendRows,appendFuel,H5,A5,Nat.zero_mul,List.replicate_zero,fuel] using joined

theorem rewind_rows (R N n pos : Nat) (bank : List Bool) :
    Step backRows (rewindFuel R N n) (H5 (pos+(n+1)*(N*(2*R)))) (A5 R N n bank)
      (H5 pos) (A5 R N n bank) := by
  let block:=N*(2*R)
  have localStep (i : Nat) (hi : i<n) : Step backRow (backFuel R N)
      (heads (pos+(n+1-i)*block)) (tapes R N bank)
      (heads (pos+(n+1-(i+1))*block)) (tapes R N bank) := by
    have h:=back_row R N (pos+(n+1-(i+1))*block) bank
    have hn : n+1-i=(n+1-(i+1))+1 := by omega
    rw [hn,Nat.add_mul,Nat.one_mul,←Nat.add_assoc]
    exact h
  have first:=PhysicalRepeatStep.run backRow n (backFuel R N)
    (fun i=>heads (pos+(n+1-i)*block)) (fun _=>tapes R N bank) localStep
  have last:=(back_row R N pos bank).embed (fun _ : Fin 1=>1)
    (fun _ : Fin 1=>CompareMachine.word n)
  have hn : n+1-n=1 := by omega
  simp only [Nat.sub_zero,hn,Nat.one_mul] at first
  have joined:=first.seq last
  have fuel : n*(backFuel R N+3)+3+1=n*(backFuel R N+3)+4 := by omega
  simpa only [backRows,rewindFuel,H5,A5,fuel] using joined

theorem run (R N n : Nat) :
    Step machine (budget R N n) (H5 0) (A5 R N n [])
      (H5 0) (A5 R N n (List.replicate ((n+1)*(N*(2*R))) false)) := by
  have first:=append_rows R N n
  have second:=rewind_rows R N n 0 (List.replicate ((n+1)*(N*(2*R))) false)
  simp only [Nat.zero_add] at second
  exact first.seq second

def paddedTapes (R S N n : Nat) (bank : List Bool) : Fin 5→List Bool :=
  ![ZeroPadding.pad S (UnaryTemplate.tape R),bank,List.replicate S false,
    ZeroPadding.pad S (CompareMachine.word N),CompareMachine.word n]

theorem padded_run (R S N n : Nat) :
    Step machine (budget R N n) (H5 0) (paddedTapes R S N n [])
      (H5 0) (paddedTapes R S N n (List.replicate ((n+1)*(N*(2*R))) false)) := by
  have padded:=(run R N n).pad (![S,0,S,S,0] : Fin 5→Nat)
  have eqn (bank : List Bool) :
      (fun i=>ZeroPadding.pad ((![S,0,S,S,0] : Fin 5→Nat) i) (A5 R N n bank i))=
      paddedTapes R S N n bank := by
    have layout : A5 R N n bank=
        ![UnaryTemplate.tape R,bank,[],CompareMachine.word N,CompareMachine.word n] := by
      funext i;fin_cases i <;>rfl
    rw [layout]
    funext i;fin_cases i <;> simp [paddedTapes,ZeroPadding.pad_zero,ZeroPadding.pad]
  exact (padded.congr_in rfl (eqn [])).congr rfl (eqn _)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalZeroRectangle

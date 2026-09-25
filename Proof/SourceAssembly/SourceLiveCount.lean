import Proof.SourceAssembly.SourceLog

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourceLiveCount
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open PCJ6e421fabe2aa4155_SourceLog SupplierPipeline SupplierEstimator
noncomputable section

theorem product_step (L e : Nat) : Step ClockUnaryProduct.machine (2*(L*(2*e+3)+2)+2)
    (fun _=>0) ![List.replicate L true,CompareMachine.word e,[],[]] (fun _=>0)
    ![List.replicate L true,CompareMachine.word e,List.replicate (L*e) true,List.replicate (L*(2*e+3)+2) false] := by
  obtain ⟨r,hr,h0,h1,h2,h3,hh,hs⟩:=ClockUnaryProduct.product_run L e
  have hi : (Fin.addCases (motive:=fun _ : Fin 4=>List Bool)
      ![List.replicate L true,false::List.replicate e true,[]] (fun _ : Fin 1=>[]))=
      ![List.replicate L true,CompareMachine.word e,[],[]] := by
    funext i;fin_cases i <;>rfl
  rw [hi] at hr
  refine ⟨r,hr,funext hh,?_,hs.le⟩
  funext i;fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem unary_pad (n : Nat) : UnaryTemplate.tape n=ZeroPadding.pad (n+2) (CompareMachine.word n) := by
  simp [UnaryTemplate.tape,ZeroPadding.pad,CompareMachine.word]

theorem split_step (q w : Nat) : ∃ k,Step PCJ6e421fabe2aa4155_SourceLiveMin.split (2*q+6)
    (fun _=>0) ![CompareMachine.word q,UnaryTemplate.tape w,[],[],[]] (fun _=>0)
    ![CompareMachine.word q,UnaryTemplate.tape w,List.replicate (min q w) true,
      List.replicate (q-w) true,List.replicate k false] ∧k≤q+2 := by
  obtain ⟨k,h,hk⟩:=PCJ6e421fabe2aa4155_SourceLiveMin.split_run q w
  have actual:=h.pad (![0,w+2,0,0,0])
  refine ⟨k,actual.congr_in rfl ?_ |>.congr rfl ?_,hk⟩
  all_goals funext i;fin_cases i <;>simp [ZeroPadding.pad_zero,←unary_pad]

def fixedSlots : Fin 2→Fin 27:=![16,17]
def productSlots : Fin 4→Fin 27:=![16,14,18,19]
def templateSlots : Fin 3→Fin 27:=![18,20,21]
def splitSlots : Fin 5→Fin 27:=![0,20,22,23,24]
def finalSlots : Fin 3→Fin 27:=![22,25,26]
def first:=TapeEmbedding.machine 11 PCJ6e421fabe2aa4155_SourceLog.machine
def fixed (L : Nat):=RecoveryFocus.machine fixedSlots (HierarchyFixedWord.machine (List.replicate L true))
def product:=RecoveryFocus.machine productSlots ClockUnaryProduct.machine
def template:=RecoveryFocus.machine templateSlots (DimensionTemplate.machine false)
def split:=RecoveryFocus.machine splitSlots PCJ6e421fabe2aa4155_SourceLiveMin.split
def last:=RecoveryFocus.machine finalSlots (DimensionTemplate.machine false)
def machine (L : Nat):=Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (Composition.machine first (fixed L)) product) template) split) last

def input (q : Nat) : Fin 27→List Bool:=Fin.addCases (motive:=fun _=>List Bool)
  (PCJ6e421fabe2aa4155_SourceLog.input q) (fun _ : Fin 11=>[])
def budget (q L : Nat):=
  ((((PCJ6e421fabe2aa4155_SourceLog.budget q+1+(2*L+2))+1+(2*(L*(2*logScale q+3)+2)+2))+1+
    (2*(L*logScale q)+8))+1+(2*q+6))+1+(2*normalizedLiveCount q L+8)

theorem run (q L : Nat) : ∃ A,Step (machine L) (budget q L) (fun _=>0) (input q) (fun _=>0) A ∧
    A 0=CompareMachine.word q ∧A 25=UnaryTemplate.tape (normalizedLiveCount q L) := by
  obtain ⟨B,hb,b0,b14⟩:=PCJ6e421fabe2aa4155_SourceLog.run q
  let A0 : Fin 27→List Bool:=Fin.addCases (motive:=fun _=>List Bool) B (fun _ : Fin 11=>[])
  have he : (Fin.addCases (motive:=fun _ : Fin 27=>Nat) (fun _ : Fin 16=>0) (fun _ : Fin 11=>0))=(fun _=>0):=by
    funext i;refine Fin.addCases (m:=16) (n:=11) (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]
  have h0:Step first _ (fun _=>0) (input q) (fun _=>0) A0:=
    ((hb.embed (fun _ : Fin 11=>0) (fun _=>[])).congr_in he rfl).congr he rfl
  have blank0:∀ i : Fin 27,16≤ i.val→A0 i=[]:=by
    intro i hi
    have hv:i=(⟨i.val-16,by omega⟩ : Fin 11).natAdd 16:=Fin.ext (by simp;omega)
    rw [hv];simp only [A0,Fin.addCases_right]
  have hfixed:=Step.of_ready (HierarchyFixedWord.word_ready (List.replicate L true))
  have h1:=dock_zero hfixed fixedSlots (by decide) A0 (by intro i;fin_cases i <;>exact blank0 _ (by decide))
  let A1:=install fixedSlots A0 (![List.replicate L true,List.replicate L false])
  simp only [List.length_replicate] at h1
  have blank1:∀ i : Fin 27,18≤ i.val→A1 i=[]:=
    install_blank fixedSlots A0 _ (old:=16) (by omega) (by decide) blank0
  have p16:A1 16=List.replicate L true:=install_slot fixedSlots (by decide) A0 _ 0
  have p14:A1 14=CompareMachine.word (logScale q):=
    (install_other fixedSlots A0 _ 14 (by decide)).trans b14
  have h2:=dock_zero (product_step L (logScale q)) productSlots (by decide) A1 (by
    intro i;fin_cases i
    · exact p16
    · exact p14
    · exact blank1 18 (by decide)
    · exact blank1 19 (by decide))
  let w:=L*logScale q
  let A2:=install productSlots A1 (![List.replicate L true,CompareMachine.word (logScale q),
    List.replicate w true,List.replicate (L*(2*logScale q+3)+2) false])
  have blank2:∀ i : Fin 27,20≤ i.val→A2 i=[]:=
    install_blank productSlots A1 _ (old:=18) (by omega) (by decide) blank1
  have p18:A2 18=List.replicate w true:=install_slot productSlots (by decide) A1 _ 2
  have h3:=dock_zero (clock_step (DimensionTemplate.ready false w)) templateSlots (by decide) A2 (by
    intro i;fin_cases i
    · exact p18
    · exact blank2 20 (by decide)
    · exact blank2 21 (by decide))
  let A3:=install templateSlots A2 (DimensionTemplate.output false w)
  have blank3:∀ i : Fin 27,22≤ i.val→A3 i=[]:=
    install_blank templateSlots A2 _ (old:=20) (by omega) (by decide) blank2
  have p20:A3 20=UnaryTemplate.tape w:=install_slot templateSlots (by decide) A2 _ 1
  have p0:A3 0=CompareMachine.word q:=by
    dsimp only [A3]
    rw [install_other templateSlots A2 _ 0 (by decide)]
    change install productSlots A1 _ 0=_
    rw [install_other productSlots A1 _ 0 (by decide)]
    exact (install_other fixedSlots A0 _ 0 (by decide)).trans b0
  obtain ⟨k,hk,_⟩:=split_step q w
  have h4:=dock_zero hk splitSlots (by decide) A3 (by
    intro i;fin_cases i
    · exact p0
    · exact p20
    · exact blank3 22 (by decide)
    · exact blank3 23 (by decide)
    · exact blank3 24 (by decide))
  let A4:=install splitSlots A3 (![CompareMachine.word q,UnaryTemplate.tape w,
    List.replicate (min q w) true,List.replicate (q-w) true,List.replicate k false])
  have blank4:∀ i : Fin 27,25≤ i.val→A4 i=[]:=
    install_blank splitSlots A3 _ (old:=22) (by omega) (by decide) blank3
  have p22:A4 22=List.replicate (min q w) true:=install_slot splitSlots (by decide) A3 _ 2
  have h5:=dock_zero (clock_step (DimensionTemplate.ready false (min q w))) finalSlots (by decide) A4 (by
    intro i;fin_cases i
    · exact p22
    · exact blank4 25 (by decide)
    · exact blank4 26 (by decide))
  refine ⟨_,((((h0.seq h1).seq h2).seq h3).seq h4).seq h5,?_,?_⟩
  · rw [install_other finalSlots A4 _ 0 (by decide)]
    exact install_slot splitSlots (by decide) A3 _ 0
  · exact install_slot finalSlots (by decide) A4 _ 1

end
end PCJ6e421fabe2aa4155_SourceLiveCount

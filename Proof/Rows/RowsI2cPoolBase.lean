import Proof.SourceAssembly.PoolDonorCompatible

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

section
/- Helpers copied from source-reuse-20260922: PCJ6e421fabe2aa4155_SourceLog (clock_step, dock_zero, install_blank),
PCJ6e421fabe2aa4155_SourceLiveCount (product_step, unary_pad), PCJ6e421fabe2aa4155_SourceCacheBudget (occurrence_eq, loop_eq),
PCJ6e421fabe2aa4155_SourcePoolAdmissions (magnitude). Proofs unchanged. -/
namespace RowsConstruction.I2c.Log
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding
noncomputable section

theorem clock_step {t s F : Nat} {p : Machine t s} {I O : Fin t→List Bool}
    (h : ClockJoin.ReadyRun p F I O) : Step p F (fun _=>0) I (fun _=>0) O := by
  obtain ⟨r,hr,rt,rh,rs⟩:=h
  exact ⟨r,hr,funext rh,rt,rs⟩

theorem dock_zero {t u s F : Nat} {p : Machine t s} {I O : Fin t→List Bool}
    (h : Step p F (fun _=>0) I (fun _=>0) O) (slots : Fin t→Fin u)
    (hi : Function.Injective slots) (A : Fin u→List Bool) (ha : ∀i,A (slots i)=I i) :
    Step (RecoveryFocus.machine slots p) F (fun _=>0) A (fun _=>0) (install slots A O) := by
  have hz : dockH slots (fun _=>0) (fun _=>0)=(fun _ : Fin u=>0) := by
    funext i;cases hp:RecoveryFocus.pick slots i <;>simp [dockH,hp]
  exact (h.dock slots hi (fun _=>0) A (fun _=>rfl) ha).congr hz rfl

theorem install_blank {t u cut old : Nat} (slots : Fin t→Fin u) (A : Fin u→List Bool)
    (O : Fin t→List Bool) (ho:old≤cut) (hs:∀j,(slots j).val<cut)
    (ha:∀i,old≤ i.val→A i=[]) : ∀i,cut≤ i.val→install slots A O i=[] := by
  intro i hi
  rw [install_other slots A O i (by intro j he;have hj:=hs j;rw [he] at hj;omega)]
  exact ha i (ho.trans hi)

end
end RowsConstruction.I2c.Log

namespace RowsConstruction.I2c.LiveCount
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding
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

end
end RowsConstruction.I2c.LiveCount

namespace RowsConstruction.I2c.CacheBudget
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairRepresentation P1Closure

theorem occurrence_eq (B q w : Nat) :
    PoolEntryOccurrence.budget B q w=409600*(B+q+w+1)^2+4*B+22 := by
  unfold PoolEntryOccurrence.budget PoolEntryBaseline.budget PoolEntry.uniformBudget PoolEntry.reserve
  ring

theorem loop_eq (N B q w : Nat) :
    PoolEntryLoop.budget N B q w=N*(409600*(B+q+w+1)^2+4*B+25)+3 := by
  simp only [PoolEntryLoop.budget,occurrence_eq]

end RowsConstruction.I2c.CacheBudget

namespace RowsConstruction.I2c.PoolAdmissions
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound SupplierPipeline SupplierEstimator CompilerSemantics RepairSource.VerifierDecoding
noncomputable section

theorem magnitude {q B : Nat} (g : SupportedNormalizedGate q)
    (hb : (CloseoutRowsCircuitBottom.nativeWord g).length≤B) :
    (g.gate.threshold-1).natAbs+(∑i,(g.gate.weight i).natAbs)<2^(B+q+1) := by
  let e : ExactThresholdGate q:=⟨g.gate.weight,g.gate.threshold-1⟩
  have hm:=RowCachedEquation.equation_magnitude e
  have hm' : (g.gate.threshold-1).natAbs+(∑i,(g.gate.weight i).natAbs)<2^(exactWord e).length := by
    simpa only [SupplierPrime.equationMagnitudeBound,RowCachedEquation.equation,e,Nat.add_comm] using hm
  apply hm'.trans_le
  apply Nat.pow_le_pow_right (by decide)
  have he : natWord q++exactWord e=CloseoutRowsCircuitBottom.nativeWord g := by
    simp [e,exactWord,CloseoutRowsCircuitBottom.nativeWord,thresholdWord,
      CloseoutRowsGateSource.request,nonStrictAsStrict,List.append_assoc]
  have hl:=congrArg List.length he
  simp only [List.length_append] at hl
  omega

end
end RowsConstruction.I2c.PoolAdmissions
end

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolDrivers.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolDrivers
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open RowsConstruction.I2c.Log (clock_step dock_zero install_blank)
noncomputable section
local instance : NeZero (DimensionPolynomial.tapes 2):=⟨by decide⟩

def qSlots : Fin 3→Fin 28:=![0,2,3]
def sumSlots : Fin 4→Fin 28:=![1,2,4,5]
def templateSlots : Fin 3→Fin 28:=![4,6,7]
def widthSlots : Fin 3→Fin 28:=![6,8,9]
def powerSlots (i : Fin (DimensionPolynomial.tapes 2)) : Fin 28:=if i=0 then 4 else ⟨10+i.val,by have hi:i.val<18:=i.isLt;omega⟩
theorem power_inj : Function.Injective powerSlots:=by decide

def first:=RecoveryFocus.machine qSlots (UWalkUnary.machine false false)
def sum:=RecoveryFocus.machine sumSlots ClockUnarySum.machine
def template:=RecoveryFocus.machine templateSlots (DimensionTemplate.machine true)
def width:=RecoveryFocus.machine widthSlots (UWalkUnary.machine false false)
def power:=RecoveryFocus.machine powerSlots (PCPSerializerCapacity.Power.machine 2 262144)
def machine:=Composition.machine (Composition.machine (Composition.machine (Composition.machine first sum) template) width) power
def input (q B : Nat) (i : Fin 28) : List Bool:=if i=0 then CompareMachine.word q else if i=1 then List.replicate B true else []
def budget (q B : Nat):=(2*q+6)+1+(2*(B+q)+6)+1+(2*(B+q)+8)+1+(2*(B+q+1)+6)+1+PCPSerializerCapacity.Power.budget 2 262144 (B+q)

theorem run (q B : Nat) : ∃ A,Step machine (budget q B) (fun _=>0) (input q B) (fun _=>0) A ∧
    A 0=CompareMachine.word q ∧A 1=List.replicate B true ∧
    A 4=List.replicate (B+q) true ∧A 6=UnaryTemplate.tape (B+q+1) ∧
    A 8=List.replicate (B+q+1) true ∧A 17=List.replicate (65536*(B+q+(B+q+1)+1)^2) true := by
  have hq:=dock_zero (clock_step (UWalkUnary.ready false false 0 q)) qSlots (by decide) (input q B) (by
    intro i;fin_cases i <;>simp [qSlots,input,UWalkUnary.input,UWalkUnary.source,ZeroPadding.pad_zero])
  let A1:=install qSlots (input q B) (UWalkUnary.result false false 0 q)
  have fresh1 : ∀i : Fin 28,4≤ i.val→A1 i=[]:=
    install_blank qSlots (input q B) _ (old:=2) (by omega) (by decide)
      (by intro i hi;have h0:i≠0:=by intro he;subst i;contradiction
          have h1:i≠1:=by intro he;subst i;contradiction
          simp only [input,if_neg h0,if_neg h1])
  have hq0:A1 0=CompareMachine.word q:=by
    have h:=install_slot qSlots (by decide) (input q B) (UWalkUnary.result false false 0 q) 0
    change A1 0=UWalkUnary.source 0 q at h
    simpa only [UWalkUnary.source,ZeroPadding.pad_zero] using h
  have hB1:A1 1=List.replicate B true:=(install_other qSlots _ _ 1 (by decide)).trans (by simp [input])
  have hs:=dock_zero (clock_step (ClockUnarySum.sum_ready B q)) sumSlots (by decide) A1 (by
    intro i;fin_cases i
    · exact hB1
    · change A1 2=List.replicate q true
      have h:=install_slot qSlots (by decide) (input q B) (UWalkUnary.result false false 0 q) 1
      change A1 2=UWalkUnary.output false false q at h
      simpa only [UWalkUnary.output,UWalkUnary.lead,Bool.toNat_false,Nat.add_zero,Bool.false_eq_true,if_false,List.nil_append] using h
    · exact fresh1 4 (by decide)
    · exact fresh1 5 (by decide))
  let A2:=install sumSlots A1 (![List.replicate B true,List.replicate q true,List.replicate (B+q) true,List.replicate (B+q+2) false])
  have fresh2 : ∀i : Fin 28,6≤ i.val→A2 i=[]:=install_blank sumSlots A1 _ (old:=4) (by omega) (by decide) fresh1
  have ht:=dock_zero (clock_step (DimensionTemplate.ready true (B+q))) templateSlots (by decide) A2 (by
    intro i;fin_cases i
    · exact install_slot sumSlots (by decide) A1 _ 2
    · exact fresh2 6 (by decide)
    · exact fresh2 7 (by decide))
  let A3:=install templateSlots A2 (DimensionTemplate.output true (B+q))
  have fresh3 : ∀i : Fin 28,8≤ i.val→A3 i=[]:=install_blank templateSlots A2 _ (old:=6) (by omega) (by decide) fresh2
  have h6:A3 6=UnaryTemplate.tape (B+q+1):=install_slot templateSlots (by decide) A2 _ 1
  have hw:=dock_zero (clock_step (UWalkUnary.ready false false (B+q+1+2) (B+q+1))) widthSlots (by decide) A3 (by
    intro i;fin_cases i
    · change A3 6=UWalkUnary.source (B+q+1+2) (B+q+1)
      rw [h6,RowsConstruction.I2c.LiveCount.unary_pad]
      rfl
    · exact fresh3 8 (by decide)
    · exact fresh3 9 (by decide))
  let A4:=install widthSlots A3 (UWalkUnary.result false false (B+q+1+2) (B+q+1))
  have fresh4 : ∀i : Fin 28,10≤ i.val→A4 i=[]:=install_blank widthSlots A3 _ (old:=8) (by omega) (by decide) fresh3
  have h4:A4 4=List.replicate (B+q) true:=
    (install_other widthSlots A3 _ 4 (by decide)).trans (install_slot templateSlots (by decide) A2 _ 0)
  obtain ⟨P,hp,p0,pout⟩:=PCPSerializerCapacity.Power.capacity_run 2 262144 (B+q)
  have hp':=dock_zero (clock_step hp) powerSlots power_inj A4 (by
    intro i;by_cases hi:i=0
    · subst i;exact h4
    · have hv:i.val≠0:=by intro he;exact hi (Fin.ext he)
      rw [powerSlots,if_neg hi,fresh4 _ (by change 10≤10+i.val;omega)]
      simp only [DimensionPolynomial.input,hv,if_false])
  refine ⟨_,(((hq.seq hs).seq ht).seq hw).seq hp',?_,?_,?_,?_,?_,?_⟩
  · rw [install_other powerSlots A4 P 0 (by decide)]
    exact (install_other widthSlots A3 _ 0 (by decide)).trans
      ((install_other templateSlots A2 _ 0 (by decide)).trans
        ((install_other sumSlots A1 _ 0 (by decide)).trans hq0))
  · rw [install_other powerSlots A4 P 1 (by decide)]
    exact (install_other widthSlots A3 _ 1 (by decide)).trans
      ((install_other templateSlots A2 _ 1 (by decide)).trans
        (install_slot sumSlots (by decide) A1 _ 0))
  · exact (install_slot powerSlots power_inj A4 P 0).trans p0
  · rw [install_other powerSlots A4 P 6 (by decide)]
    have h:=install_slot widthSlots (by decide) A3 (UWalkUnary.result false false (B+q+1+2) (B+q+1)) 0
    change A4 6=UWalkUnary.source (B+q+1+2) (B+q+1) at h
    simpa only [UWalkUnary.source,RowsConstruction.I2c.LiveCount.unary_pad] using h
  · rw [install_other powerSlots A4 P 8 (by decide)]
    have h:=install_slot widthSlots (by decide) A3 (UWalkUnary.result false false (B+q+1+2) (B+q+1)) 1
    change A4 8=UWalkUnary.output false false (B+q+1) at h
    simpa only [UWalkUnary.output,UWalkUnary.lead,Bool.toNat_false,Nat.add_zero,Bool.false_eq_true,if_false,List.nil_append] using h
  · have h:=(install_slot powerSlots power_inj A4 P (PCPSerializerCapacity.Power.outputSlot 2)).trans pout
    have he:262144*(B+q+1)^2=65536*(B+q+(B+q+1)+1)^2:=by ring
    rw [he] at h
    exact h

end
end RowsConstruction.I2c.PoolDrivers
end

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolScalars.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolScalars
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.ProjectionNormalization
open RowsConstruction.I2c.Log (clock_step dock_zero install_blank)
noncomputable section
local instance : NeZero (DimensionPower.tapes 1):=⟨by decide⟩

def powerSlots (i : Fin (DimensionPower.tapes 1)) : Fin 14:=if i=0 then 0 else ⟨i.val+1,by have hi:i.val<5:=i.isLt;omega⟩
def fixedSlots : Fin 2→Fin 14:=![6,7]
def sumSlots : Fin 4→Fin 14:=![4,6,8,9]
def zeroSlots : Fin 5→Fin 14:=![1,10,11,12,13]
theorem power_inj : Function.Injective powerSlots:=by decide

def power:=RecoveryFocus.machine powerSlots (DimensionPower.machine 1 8)
def fixed:=RecoveryFocus.machine fixedSlots (HierarchyFixedWord.machine (List.replicate 12 true))
def sum:=RecoveryFocus.machine sumSlots ClockUnarySum.machine
def zero:=RecoveryFocus.machine zeroSlots ClockNormalize.machine
def machine:=Composition.machine (Composition.machine (Composition.machine power fixed) sum) zero
def input (w : Nat) (i : Fin 14):=if i=0 then UnaryTemplate.tape w else if i=1 then List.replicate w true else []
def budget (w : Nat):=DimensionPower.cost 8 w 1+1+26+1+(2*(8*w+12)+6)+1+(4*w+4)

theorem zero_step (w : Nat) : ∃ A,Step ClockNormalize.machine (4*w+4) (fun _=>0)
    (ClockScalarFields.zeroInput w) (fun _=>0) A ∧A 0=List.replicate w true ∧A 2=frame (SignedSortKey.binary w 0) := by
  obtain ⟨r,hr,h0,_h1,h2,_h3,_h4,hh,hs⟩:=ClockScalarFields.zero_run w
  exact ⟨r.final.tapes,⟨r,hr,funext hh,rfl,hs.le⟩,h0,h2⟩

theorem run (w : Nat) : ∃ A,Step machine (budget w) (fun _=>0) (input w) (fun _=>0) A ∧
    A 0=UnaryTemplate.tape w ∧A 1=List.replicate w true ∧
    A 8=List.replicate (8*w+12) true ∧A 11=frame (SignedSortKey.binary w 0) := by
  obtain ⟨P,hp,p0,pv⟩:=DimensionPower.power_run 1 8 w
  have hp':=dock_zero (clock_step hp) powerSlots power_inj (input w) (by
    intro i;by_cases hi:i=0
    · subst i;rfl
    · have hv:i.val≠0:=by intro he;exact hi (Fin.ext he)
      have h0:powerSlots i≠0:=by unfold powerSlots;rw [if_neg hi];intro he;have h:=congrArg Fin.val he;simp only [Fin.val_zero] at h;omega
      have h1:powerSlots i≠1:=by unfold powerSlots;rw [if_neg hi];intro he;have h:=congrArg Fin.val he;simp only [Fin.val_one] at h;omega
      simp only [input,if_neg h0,if_neg h1,DimensionPower.input,hv,if_false])
  let A1:=install powerSlots (input w) P
  have fresh1 : ∀i : Fin 14,6≤ i.val→A1 i=[]:=
    install_blank powerSlots (input w) P (old:=2) (by omega) (by decide)
      (by intro i hi;have h0:i≠0:=by intro he;subst i;contradiction
          have h1:i≠1:=by intro he;subst i;contradiction
          simp only [input,if_neg h0,if_neg h1])
  have h0:A1 0=UnaryTemplate.tape w:=(install_slot powerSlots power_inj (input w) P 0).trans p0
  have h4:A1 4=List.replicate (8*w) true:=by
    have h:=(install_slot powerSlots power_inj (input w) P (DimensionPower.valueSlot 1 1 le_rfl)).trans pv
    change A1 4=List.replicate (8*w^1) true at h
    simpa only [pow_one] using h
  obtain ⟨r,hr,rt,rh,rs⟩:=HierarchyFixedWord.word_ready (List.replicate 12 true)
  have hf0 : Step (HierarchyFixedWord.machine (List.replicate 12 true)) 26 (fun _=>0) (fun _=>[])
      (fun _=>0) (![List.replicate 12 true,List.replicate 12 false]) := by
    exact ⟨r,hr,funext rh,rt,rs.le⟩
  have hf:=dock_zero hf0 fixedSlots (by decide) A1 (by intro i;fin_cases i <;>exact fresh1 _ (by decide))
  let A2:=install fixedSlots A1 (![List.replicate 12 true,List.replicate 12 false])
  have fresh2 : ∀i : Fin 14,8≤ i.val→A2 i=[]:=install_blank fixedSlots A1 _ (old:=6) (by omega) (by decide) fresh1
  have hs:=dock_zero (clock_step (ClockUnarySum.sum_ready (8*w) 12)) sumSlots (by decide) A2 (by
    intro i;fin_cases i
    · exact (install_other fixedSlots A1 _ 4 (by decide)).trans h4
    · exact install_slot fixedSlots (by decide) A1 _ 0
    · exact fresh2 8 (by decide)
    · exact fresh2 9 (by decide))
  let A3:=install sumSlots A2 (![List.replicate (8*w) true,List.replicate 12 true,List.replicate (8*w+12) true,List.replicate (8*w+12+2) false])
  have fresh3 : ∀i : Fin 14,10≤ i.val→A3 i=[]:=install_blank sumSlots A2 _ (old:=8) (by omega) (by decide) fresh2
  have h1:A3 1=List.replicate w true:=
    (install_other sumSlots A2 _ 1 (by decide)).trans ((install_other fixedSlots A1 _ 1 (by decide)).trans
      ((install_other powerSlots (input w) P 1 (by decide)).trans (by simp [input])))
  obtain ⟨Z,hz,z0,z2⟩:=zero_step w
  have hz':=dock_zero hz zeroSlots (by decide) A3 (by
    intro i;fin_cases i
    · exact h1
    all_goals exact fresh3 _ (by decide))
  refine ⟨_,((hp'.seq hf).seq hs).seq hz',?_,?_,?_,?_⟩
  · exact (install_other zeroSlots A3 Z 0 (by decide)).trans
      ((install_other sumSlots A2 _ 0 (by decide)).trans ((install_other fixedSlots A1 _ 0 (by decide)).trans h0))
  · exact (install_slot zeroSlots (by decide) A3 Z 0).trans z0
  · exact (install_other zeroSlots A3 Z 8 (by decide)).trans (install_slot sumSlots (by decide) A2 _ 2)
  · exact (install_slot zeroSlots (by decide) A3 Z 2).trans z2

end
end RowsConstruction.I2c.PoolScalars
end

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolCapacity.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolCapacity
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal RepairSource.VerifierDecoding
noncomputable section

def value (B q : Nat):=16777216*(B+q+1)^3

theorem arithmetic (N B q : Nat) (hn:N≤B) :
    4*N+4+PoolEntryLoop.budget N B q (B+q+1)≤value B q := by
  let w:=B+q+1
  have hw:1≤w:=by omega
  have hn':N≤w:=by omega
  have hb:B≤w:=by omega
  have hw2:w≤w^2:=by nlinarith
  have hw3:w^2≤w^3:=by have h:=Nat.mul_le_mul_right (w^2) hw;simpa only [one_mul,pow_succ,Nat.mul_comm] using h
  rw [RowsConstruction.I2c.CacheBudget.loop_eq]
  have he:B+q+(B+q+1)+1=2*w:=by omega
  rw [he]
  have hm:=Nat.mul_le_mul hn' (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 4 hb) (409600*(2*w)^2)) 25)
  unfold value
  change 4*N+4+(N*(409600*(2*w)^2+4*B+25)+3)≤16777216*w^3
  nlinarith

theorem segment_bound {q : Nat} (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (B : Nat) (hn:occ.length≤B)
    (hb:∀g∈occ,(CloseoutRowsCircuitBottom.nativeWord g).length≤B) :
    (segment (CloseoutRowsUniversal.pool live occ) []).length≤value B q := by
  obtain ⟨r,hr,hf,hs⟩:=PoolEntryLoop.segment_run live occ B (B+q+1) []
    (by omega) (by omega) hb (fun g hg=>RowsConstruction.I2c.PoolAdmissions.magnitude g (hb g hg))
  have hh:=SelectiveReset.prefix_head (prefix_of_run _ _ _ r hr).1 (61 : Fin 132)
  rw [hf] at hh
  change (segment (CloseoutRowsUniversal.pool live occ) []).length≤
    (natWord (2*occ.length)++RepairOrdinary.frame []).length+r.steps at hh
  have hnw:natBitLength (2*occ.length)≤2*occ.length+1:=Nat.add_le_add_right (Nat.log_le_self 2 (2*occ.length)) 1
  have hp:(natWord (2*occ.length)++RepairOrdinary.frame []).length≤4*occ.length+4:=by
    simp only [List.length_append,DecompositionSource.natWord_length,frame_length,List.length_nil] at *
    omega
  exact hh.trans ((Nat.add_le_add hp hs).trans (arithmetic occ.length B q hn))

theorem small_bounds (B q : Nat) : q+2≤value B q ∧
    PoolEntry.reserve B q (B+q+1)+1≤value B q ∧8*(B+q+1)+12≤value B q := by
  have hw:1≤B+q+1:=by omega
  have h2:B+q+1≤(B+q+1)^2:=by nlinarith
  have h3:(B+q+1)^2≤(B+q+1)^3:=by
    have h:=Nat.mul_le_mul_right ((B+q+1)^2) hw
    simpa only [one_mul,pow_succ,Nat.mul_comm] using h
  unfold value PoolEntry.reserve
  constructor
  · nlinarith
  constructor <;>nlinarith

end
end RowsConstruction.I2c.PoolCapacity
end

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolPreparation.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolPreparation
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
open RowsConstruction.I2c.Log (clock_step dock_zero install_blank)
noncomputable section
local instance : NeZero (DimensionPolynomial.tapes 3):=⟨by decide⟩

def scalarSlots (i : Fin 14) : Fin 62:=if i=0 then 6 else if i=1 then 8 else ⟨28+i.val,by omega⟩
-- The input dimension is20; the unused slot42 remains blank.
def powerSlots (i : Fin (DimensionPolynomial.tapes 3)) : Fin 62:=if i=0 then 4 else ⟨42+i.val,by have hi:i.val<20:=i.isLt;omega⟩
theorem scalar_inj : Function.Injective scalarSlots:=by decide
theorem power_inj : Function.Injective powerSlots:=by decide

def first:=TapeEmbedding.machine 34 RowsConstruction.I2c.PoolDrivers.machine
def scalars:=RecoveryFocus.machine scalarSlots RowsConstruction.I2c.PoolScalars.machine
def power:=RecoveryFocus.machine powerSlots (PCPSerializerCapacity.Power.machine 3 16777216)
def machine:=Composition.machine (Composition.machine first scalars) power
def input (q B : Nat) : Fin 62→List Bool:=Fin.addCases (motive:=fun _=>List Bool)
  (RowsConstruction.I2c.PoolDrivers.input q B) (fun _ : Fin 34=>[])
def budget (q B : Nat):=RowsConstruction.I2c.PoolDrivers.budget q B+1+
  RowsConstruction.I2c.PoolScalars.budget (B+q+1)+1+
  PCPSerializerCapacity.Power.budget 3 16777216 (B+q)

theorem run (q B : Nat) : ∃ A,Step machine (budget q B) (fun _=>0) (input q B) (fun _=>0) A ∧
    A 0=CompareMachine.word q ∧A 1=List.replicate B true ∧
    A 6=UnaryTemplate.tape (B+q+1) ∧A 8=List.replicate (B+q+1) true ∧
    A 36=List.replicate (8*(B+q+1)+12) true ∧
    A 39=frame (SignedSortKey.binary (B+q+1) 0) ∧
    A 17=List.replicate (65536*(B+q+(B+q+1)+1)^2) true ∧
    A 51=List.replicate (RowsConstruction.I2c.PoolCapacity.value B q) true := by
  obtain ⟨D,hd,d0,d1,d4,d6,d8,d17⟩:=RowsConstruction.I2c.PoolDrivers.run q B
  let A1 : Fin 62→List Bool:=Fin.addCases (motive:=fun _=>List Bool) D (fun _ : Fin 34=>[])
  have hf:Step first _ (fun _=>0) (input q B) (fun _=>0) A1:=
    (hd.embed (fun _ : Fin 34=>0) (fun _=>[])).congr_in
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl |>.congr
      (by funext i;refine Fin.addCases (fun _=>?_) (fun _=>?_) i <;>simp only [Fin.addCases_left,Fin.addCases_right]) rfl
  have blank1 : ∀i : Fin 62,28≤ i.val→A1 i=[] := by
    intro i hi
    have he:i=(⟨i.val-28,by omega⟩ : Fin 34).natAdd 28:=Fin.ext (by simp;omega)
    rw [he]
    change Fin.addCases (motive:=fun _=>List Bool) D (fun _ : Fin 34=>[]) _=[]
    rw [Fin.addCases_right]
  obtain ⟨S,hs,s0,s1,s8,s11⟩:=RowsConstruction.I2c.PoolScalars.run (B+q+1)
  have selected:∀i,A1 (scalarSlots i)=RowsConstruction.I2c.PoolScalars.input (B+q+1) i := by
    intro i;by_cases h0:i=0
    · subst i;exact d6
    by_cases h1:i=1
    · subst i;exact d8
    rw [scalarSlots,if_neg h0,if_neg h1,blank1 _ (by simp)]
    simp only [RowsConstruction.I2c.PoolScalars.input,if_neg h0,if_neg h1]
  have hs':=dock_zero hs scalarSlots scalar_inj A1 selected
  let A2:=install scalarSlots A1 S
  have blank2 : ∀i : Fin 62,42≤ i.val→A2 i=[]:=install_blank scalarSlots A1 S (old:=28) (by omega) (by decide) blank1
  obtain ⟨P,hp,_p0,pv⟩:=PCPSerializerCapacity.Power.capacity_run 3 16777216 (B+q)
  have hp':=dock_zero (clock_step hp) powerSlots power_inj A2 (by
    intro i;by_cases hi:i=0
    · subst i
      exact (install_other scalarSlots A1 S 4 (by decide)).trans d4
    · have hv:i.val≠0:=by intro he;exact hi (Fin.ext he)
      rw [powerSlots,if_neg hi,blank2 _ (by change 42≤42+i.val;omega)]
      simp only [DimensionPolynomial.input,hv,if_false])
  refine ⟨_,(hf.seq hs').seq hp',?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (install_other powerSlots A2 P 0 (by decide)).trans ((install_other scalarSlots A1 S 0 (by decide)).trans d0)
  · exact (install_other powerSlots A2 P 1 (by decide)).trans ((install_other scalarSlots A1 S 1 (by decide)).trans d1)
  · exact (install_other powerSlots A2 P 6 (by decide)).trans ((install_slot scalarSlots scalar_inj A1 S 0).trans s0)
  · exact (install_other powerSlots A2 P 8 (by decide)).trans ((install_slot scalarSlots scalar_inj A1 S 1).trans s1)
  · exact (install_other powerSlots A2 P 36 (by decide)).trans ((install_slot scalarSlots scalar_inj A1 S 8).trans s8)
  · exact (install_other powerSlots A2 P 39 (by decide)).trans ((install_slot scalarSlots scalar_inj A1 S 11).trans s11)
  · exact (install_other powerSlots A2 P 17 (by decide)).trans ((install_other scalarSlots A1 S 17 (by decide)).trans d17)
  · exact (install_slot powerSlots power_inj A2 P (PCPSerializerCapacity.Power.outputSlot 3)).trans pv

end
end RowsConstruction.I2c.PoolPreparation
end

section
/- Copied from source-reuse-20260922/PCJ6e421fabe2aa4155_SourcePoolHeader.lean (namespace renamed; see module header). -/
namespace RowsConstruction.I2c.PoolHeader
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding
open RowsConstruction.I2c.Log (clock_step dock_zero install_blank)
noncomputable section

def fixedSlots : Fin 2→Fin 20:=![1,2]
def productSlots : Fin 4→Fin 20:=![1,0,3,4]
def headerSlots (i : Fin 16) : Fin 20:=if i=0 then 3 else ⟨i.val+4,by omega⟩
theorem header_inj : Function.Injective headerSlots:=by decide
def fixed:=RecoveryFocus.machine fixedSlots (HierarchyFixedWord.machine [true,true])
def product:=RecoveryFocus.machine productSlots ClockUnaryProduct.machine
def header:=RecoveryFocus.machine headerSlots EquationNaturalHeader.machine
def machine:=Composition.machine (Composition.machine fixed product) header
def input (N : Nat) : Fin 20→List Bool:=fun i=>if i=0 then CompareMachine.word N else []
def budget (N : Nat):=6+1+(2*(2*(2*N+3)+2)+2)+1+(EquationNaturalHeader.budget (2*N)+2)

theorem run (N : Nat) : ∃ A,Step machine (budget N) (fun _=>0) (input N) (fun _=>0) A ∧
    A 0=CompareMachine.word N ∧A 18=natWord (2*N) := by
  have h1:=dock_zero (Step.of_ready (HierarchyFixedWord.word_ready [true,true]))
    fixedSlots (by decide) (input N) (by intro i;fin_cases i <;>rfl)
  let A1:=install fixedSlots (input N) (![([true,true] : List Bool),[false,false]])
  have b1:∀i : Fin 20,3≤ i.val→A1 i=[]:=by
    apply install_blank fixedSlots (input N) _ (old:=1) (by omega) (by decide)
    intro i hi
    have hn:i≠0:=by intro h;subst i;contradiction
    exact if_neg hn
  have p1:A1 1=List.replicate 2 true:=install_slot fixedSlots (by decide) (input N) _ 0
  have p0:A1 0=CompareMachine.word N:=install_other fixedSlots (input N) _ 0 (by decide)
  have h2:=dock_zero (RowsConstruction.I2c.LiveCount.product_step 2 N)
    productSlots (by decide) A1 (by
      intro i;fin_cases i
      · exact p1
      · exact p0
      · exact b1 3 (by decide)
      · exact b1 4 (by decide))
  let A2:=install productSlots A1
    (![List.replicate 2 true,CompareMachine.word N,List.replicate (2*N) true,
      List.replicate (2*(2*N+3)+2) false])
  have b2:∀i : Fin 20,5≤ i.val→A2 i=[]:=
    install_blank productSlots A1 _ (old:=3) (by omega) (by decide) b1
  obtain ⟨H,hH,_h1,h14⟩:=EquationNaturalHeader.header_ready (2*N)
  have h3:=dock_zero (clock_step hH) headerSlots header_inj A2 (by
    intro i;by_cases hi:i=0
    · subst i;exact install_slot productSlots (by decide) A1 _ 2
    · rw [headerSlots,if_neg hi,b2 _ (by
        have hn:i.val≠0:=by intro h;exact hi (Fin.ext h)
        change 5≤ i.val+4
        omega)]
      exact (if_neg hi).symm)
  refine ⟨_,(h1.seq h2).seq h3,?_,?_⟩
  · exact (install_other headerSlots A2 H 0 (by decide)).trans
      (install_slot productSlots (by decide) A1 _ 1)
  · exact (install_slot headerSlots header_inj A2 H 14).trans h14

end
end RowsConstruction.I2c.PoolHeader
end


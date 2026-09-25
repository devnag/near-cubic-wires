import Proof.MachineModel.Layout
import Proof.Rows.FinalPrimeCoefficientReduce

/-! Paid reduction and signed selection on the actual installed tape states.
The raw MSB-first magnitude, physical sign, prime, zero words, repeat
template and reset capacities are supplied at this local input boundary. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10NativeSignedResidue
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairSource.VerifierDecoding RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def head : Fin 10 → ℕ := fun i => if i=6 then 1 else 0

def data (p w cap Q D : ℕ) (bits : List Bool) (negative : Bool)
    (r u v : List Bool) (flag : Bool) : Fin 10 → List Bool :=
  ![frame r,frame u,frame (SignedSortKey.binary w p),[flag],bits,List.replicate cap false,
    CompareMachine.word Q,frame v,[negative],List.replicate D false]

def reduceSlots : Fin 8 → Fin 10 := ![0,1,2,3,4,5,6,9]
def negateSlots : Fin 6 → Fin 10 := ![1,7,2,3,0,9]
def residueSlots : Fin 4 → Fin 10 := ![1,7,3,9]
def signSlots : Fin 4 → Fin 10 := ![0,1,8,9]
def reduceSelected : Fin 7 → Bool := fun i => decide (i≠6)
noncomputable def reduction := RecoveryFocus.machine reduceSlots
  (MaskedReset.machine FinalPrimeResidue.whole reduceSelected)
noncomputable def negation := RecoveryFocus.machine negateSlots
  (MaskedReset.machine FinalPrimeNegate.machine (fun _=>true))
noncomputable def selection := RecoveryFocus.machine residueSlots
  (MaskedReset.machine FinalPrimeResidue.machine (fun _=>true))
noncomputable def signedSelection := RecoveryFocus.machine signSlots
  (MaskedReset.machine FinalPrimeResidue.machine (fun _=>true))
noncomputable def machine := Composition.machine
  (Composition.machine (Composition.machine reduction negation) selection) signedSelection

def budget (w Q : ℕ) := 2*FinalPrimeResidue.fuel w Q+12*w+21

private theorem dock_exact {t u s n : ℕ} {p : Machine t s} {hin hout : Fin t → ℕ}
    {tin tout : Fin t → List Bool} (h : Step p n hin tin hout tout)
    (slots : Fin t → Fin u) (hi : Function.Injective slots) (H : Fin u → ℕ)
    (A B : Fin u → List Bool) (hhi : ∀ j, H (slots j)=hin j) (hho : ∀ j, H (slots j)=hout j)
    (hti : ∀ j, A (slots j)=tin j) (hto : ∀ j, B (slots j)=tout j)
    (hother : ∀ i,(∀ j,slots j≠i)→B i=A i) :
    Step (RecoveryFocus.machine slots p) n H A H B :=
  (h.dock slots hi H A hhi hti).congr (dockH_existing slots H hout hho)
    (HierarchyAllocation.install_eq slots hi A B tout hto hother)

private theorem reduce_step (p w cap Q D : ℕ) (bits : List Bool) (negative : Bool)
    (hc : 2*w+2≤cap) (hD : FinalPrimeResidue.fuel w Q≤D) :
    Step reduction (2*FinalPrimeResidue.fuel w Q+2) head
      (data p w cap Q D bits negative (SignedSortKey.binary w 0) (SignedSortKey.binary w 0)
        (SignedSortKey.binary w 0) false)
      head
      (data p w cap Q D bits negative
        (FinalPrimeRow.residueWord (FinalPrimeRow.stateAt p w bits Q))
        (FinalPrimeRow.stateAt p w bits Q).2.1 (SignedSortKey.binary w 0)
        (FinalPrimeRow.stateAt p w bits Q).2.2) := by
  let st := FinalPrimeRow.stateAt p w bits Q
  have raw := FinalPrimeResidue.whole_step p w cap Q bits hc
  have hT : (install FinalPrimeResidue.slots (FinalPrimeResidue.loopEnd p w cap Q bits).tapes
      (![frame (FinalPrimeRow.residueWord st),frame st.2.1,[st.2.2]])) =
      (![frame (FinalPrimeRow.residueWord st),frame st.2.1,frame (SignedSortKey.binary w p),
        [st.2.2],bits,List.replicate cap false,CompareMachine.word Q] : Fin 7 → List Bool) := by
    funext i; fin_cases i
    all_goals first
      | exact install_slot FinalPrimeResidue.slots FinalPrimeResidue.slots_injective _ _ 0
      | exact install_slot FinalPrimeResidue.slots FinalPrimeResidue.slots_injective _ _ 1
      | exact install_slot FinalPrimeResidue.slots FinalPrimeResidue.slots_injective _ _ 2
      | exact (install_other FinalPrimeResidue.slots _ _ _ (by decide)).trans rfl
  have normalized := raw.congr rfl hT
  have reset := normalized.mask (cap:=D) reduceSelected (by
    intro i hi; fin_cases i <;> first | rfl | contradiction) hD
  apply dock_exact reset reduceSlots (by decide) head _ _
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i hi; fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 3 rfl)



/-- The actual installed post-state is retained; only consumer ports are
projected. No flattened equality expands the computed negation words. -/
theorem run (p w cap Q D : ℕ) (bits : List Bool) (negative : Bool)
    (hc : 2*w+2≤cap) (hD : FinalPrimeResidue.fuel w Q≤D) (hs : 2*w+2≤D) :
    let st := FinalPrimeRow.stateAt p w bits Q
    let r := FinalPrimeRow.residueWord st
    let ns := FinalPrimeNegate.negState p w r
    let nr := if ns.2.2 then ns.2.1 else ns.1
    ∃ output : Fin 10 → List Bool,
      Step machine (budget w Q) head
        (data p w cap Q D bits negative (SignedSortKey.binary w 0) (SignedSortKey.binary w 0)
          (SignedSortKey.binary w 0) false) head output ∧
      output 0=frame (if negative then nr else r) ∧
      output 2=frame (SignedSortKey.binary w p) ∧ output 9=List.replicate D false := by
  dsimp only
  let st := FinalPrimeRow.stateAt p w bits Q
  let r := FinalPrimeRow.residueWord st
  let ns := FinalPrimeNegate.negState p w r
  let nr := if ns.2.2 then ns.2.1 else ns.1
  have hst := FinalPrimeRow.stateAt_length p w bits Q
  have hr : r.length=w := by
    unfold r FinalPrimeRow.residueWord
    split <;> first | exact hst.1 | exact hst.2
  have hns := FinalPrimeNegate.negState_length p w r hr
  have hnr : nr.length=w := by
    unfold nr
    split <;> first | exact hns.1 | exact hns.2
  have first := reduce_step p w cap Q D bits negative hc hD
  let A := data p w cap Q D bits negative r st.2.1 (SignedSortKey.binary w 0) st.2.2
  have neg := (FinalPrimeNegate.negate_step p w st.2.1 (SignedSortKey.binary w 0) r [st.2.2]
    hst.2 (SignedSortKey.binary_length _ _) hr).mask (cap:=D) (fun _=>true)
      (by intro i hi; fin_cases i <;> rfl) (by omega)
  have negOut := neg.congr rfl (show _ =
    (![frame ns.1,frame ns.2.1,frame (SignedSortKey.binary w p),[ns.2.2],frame r,
      List.replicate D false] : Fin 6 → List Bool) by
      funext i; fin_cases i <;> rfl)
  have second := (negOut.dock negateSlots (by decide) head A
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)).congr
      (dockH_existing negateSlots _ _ (by intro j; fin_cases j <;> rfl)) rfl
  let B := install negateSlots A
    (![frame ns.1,frame ns.2.1,frame (SignedSortKey.binary w p),[ns.2.2],frame r,
      List.replicate D false] : Fin 6 → List Bool)
  have pick := FinalPrimeResidue.select_step ns.2.2 ns.1 ns.2.1 [ns.2.2]
    (hns.2.trans hns.1.symm) rfl
  rw [hns.1] at pick
  have picked := pick.mask (cap:=D) (fun _=>true) (by intro i hi; fin_cases i <;> rfl) hs
  have pickOut := picked.congr rfl (show _ =
    (![frame nr,frame ns.2.1,[ns.2.2],List.replicate D false] : Fin 4 → List Bool) by
      funext i; fin_cases i <;> rfl)
  have third := (pickOut.dock residueSlots (by decide) head B
    (by intro j; fin_cases j <;> rfl) (by
      intro j; fin_cases j
      · exact install_slot negateSlots (by decide) _ _ 0
      · exact install_slot negateSlots (by decide) _ _ 1
      · exact install_slot negateSlots (by decide) _ _ 3
      · exact install_slot negateSlots (by decide) _ _ 5)).congr
        (dockH_existing residueSlots _ _ (by intro j; fin_cases j <;> rfl)) rfl
  let C := install residueSlots B
    (![frame nr,frame ns.2.1,[ns.2.2],List.replicate D false] : Fin 4 → List Bool)
  have choose := FinalPrimeResidue.select_step negative r nr [negative] (hnr.trans hr.symm) rfl
  rw [hr] at choose
  have chosen := choose.mask (cap:=D) (fun _=>true) (by intro i hi; fin_cases i <;> rfl) hs
  have fourth := (chosen.dock signSlots (by decide) head C
    (by intro j; fin_cases j <;> rfl) (by
      intro j; fin_cases j
      · exact (install_other residueSlots _ _ _ (by decide)).trans (install_slot negateSlots (by decide) _ _ 4)
      · exact install_slot residueSlots (by decide) _ _ 0
      · exact (install_other residueSlots _ _ _ (by decide)).trans
          ((install_other negateSlots _ _ _ (by decide)).trans rfl)
      · exact install_slot residueSlots (by decide) _ _ 3)).congr
        (dockH_existing signSlots _ _ (by intro j; fin_cases j <;> rfl)) rfl
  have complete := ((first.seq second).seq third).seq fourth
  have ht : ((2*FinalPrimeResidue.fuel w Q+2+1+(2*(2*w+1)+2))+1+(2*(2*w+2)+2))+1+
      (2*(2*w+2)+2)=budget w Q := by unfold budget; omega
  rw [ht] at complete
  refine ⟨_,complete,?_,?_,?_⟩
  · exact install_slot signSlots (by decide) _ _ 0
  · exact (install_other signSlots _ _ _ (by decide)).trans
      ((install_other residueSlots _ _ _ (by decide)).trans (install_slot negateSlots (by decide) _ _ 2))
  · exact install_slot signSlots (by decide) _ _ 3

theorem word_eq (p w Q : ℕ) (bits : List Bool) (negative : Bool)
    (hp : 0<p) (hpw : 2*p≤2^w) :
    let r := FinalPrimeRow.residueWord (FinalPrimeRow.stateAt p w bits Q)
    let nr := FinalPrimeRow.residueWord (FinalPrimeNegate.negState p w r)
    (if negative then nr else r) = SignedSortKey.binary w
      (if negative then (p-FinalPrimeRow.horner bits Q%p)%p else FinalPrimeRow.horner bits Q%p) := by
  dsimp only
  let r := FinalPrimeRow.residueWord (FinalPrimeRow.stateAt p w bits Q)
  let ns := FinalPrimeNegate.negState p w r
  let nr := FinalPrimeRow.residueWord ns
  have hst := FinalPrimeRow.stateAt_length p w bits Q
  have hr : r.length=w := by
    unfold r FinalPrimeRow.residueWord
    split <;> first | exact hst.1 | exact hst.2
  have hv : value r=FinalPrimeRow.horner bits Q%p := FinalPrimeRow.stateAt_residue p w bits Q hp hpw
  have hns := FinalPrimeNegate.negState_length p w r hr
  have hn : nr.length=w := by
    unfold nr FinalPrimeRow.residueWord
    split <;> first | exact hns.1 | exact hns.2
  have hnv : value nr=(p-FinalPrimeRow.horner bits Q%p)%p := by
    change FinalPrimeRow.residueOf (FinalPrimeNegate.negState p w r)=_
    rw [FinalPrimeNegate.negate_residue p w r hr hp hpw (by rw [hv]; exact Nat.mod_lt _ hp), hv]
  have a := BoundedCounter.binary_of_value r
  have b := BoundedCounter.binary_of_value nr
  rw [hr,hv] at a
  rw [hn,hnv] at b
  cases negative
  · exact a.symm
  · exact b.symm

end NearCubicWires.RepairSource.CloseoutFinal.C10NativeSignedResidue

import Proof.Rows.FinalNativeResidueDriver
import Proof.Rows.FinalNativeResidueReuse

namespace NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidueCallback
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def head (pos len : ℕ) : Fin 23 → ℕ := fun i=>if i=0 then pos else if i=22 then len else 0
def preparedHead (pos len : ℕ) := Function.update (head pos len) 3 1
def drivenHead (pos len : ℕ) := Function.update (head pos len) 19 1
def driverSlots : Fin 3 → Fin 23 := ![3,19,11]
def scalarSlots : Fin 10 → Fin 23 := fun i=>(C10NativeResidue.slots i).castAdd 1
noncomputable def finalHead (pos w len : ℕ) :=
  dockH C10NativeResidueAppend.slots (drivenHead pos len) ![2*w+1,len+(2*w+1)]
noncomputable def read := TapeEmbedding.machine 9 C10NativeResiduePrepare.machine
noncomputable def double := RecoveryFocus.machine driverSlots C10NativeResidueDriver.machine
noncomputable def scalar (negate : Bool) := RecoveryFocus.machine scalarSlots (C10NativeResidue.signedMachine negate)
noncomputable def core (negate : Bool) := Composition.machine
  (Composition.machine (Composition.machine read double) (scalar negate)) C10NativeResidueAppend.last

def coreBudget (negate : Bool) (z : ℤ) (w : ℕ) :=
  C10NativeResidueAppend.budget negate z w+4*natBitLength z.natAbs+11

theorem core_run (negate : Bool) (pre tail out : List Bool) (z : ℤ) (p w F : ℕ)
    (hp : 0<p) (hpw : 2*p≤2^w) (hw : 2*w+2≤F)
    (hB : 4*natBitLength z.natAbs+2≤F)
    (hD : FinalPrimeResidue.fuel w (2*natBitLength z.natAbs)≤F) :
    ∃ output : Fin 23 → List Bool,
      Step (core negate) (coreBudget negate z w) (head pre.length out.length)
        (C10NativeResidueRestore.canonical F w p (pre++intWord z++tail) out)
        (finalHead (pre.length+(intWord z).length) w out.length) output ∧
      output 0=pre++intWord z++tail ∧
      output 22=out++frame (SignedSortKey.binary w (FinalPrimeReduce.intResidue p (if negate then -z else z))) := by
  let B := natBitLength z.natAbs
  let pos := pre.length+(intWord z).length
  let bits := RecoveryRadixInput.prepared (SignedSortKey.binary B z.natAbs)
  let extra : Fin 9 → List Bool := fun i=>C10NativeResidueRestore.canonical F w p [] out (i.natAdd 14)
  obtain ⟨prepared,pr,ps,psign,pbits,pwidth,plog⟩ := C10NativeResidueDriver.prepare_run pre tail z F hB
  let A : Fin 23 → List Bool := Fin.addCases (m:=14) (n:=9) (motive:=fun _=>List Bool)
    (fun i=>ZeroPadding.pad (if i=0 then 0 else F) (prepared i)) extra
  have raw := (pr.pad (fun i=>if i=0 then 0 else F)).embed
    (fun i : Fin 9=>if i=8 then out.length else 0) extra
  have first : Step read (22*B+19) (head pre.length out.length)
      (C10NativeResidueRestore.canonical F w p (pre++intWord z++tail) out)
      (preparedHead pos out.length) A := by
    refine (raw.congr_in ?_ ?_).congr ?_ rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [C10NativeResidueRestore.canonical,C10NativeResiduePrepare.input,
        C10NativeResiduePrepare.extras,DecompositionNativeMagnitude.input,ZeroPadding.pad,extra,Fin.addCases]
    · funext i; fin_cases i <;> rfl
  have driven := (C10NativeResidueDriver.driver_run B F F (by omega) (by omega)).dock driverSlots (by decide)
    (preparedHead pos out.length) A (by intro i; fin_cases i <;> rfl) (by
      intro i; fin_cases i
      · exact congrArg (ZeroPadding.pad F) pwidth
      · rfl
      · exact (congrArg (ZeroPadding.pad F) plog).trans (pad_replicate_false F F le_rfl))
  have driver := driven.congr (show _=drivenHead pos out.length by
    funext i; fin_cases i <;> first
      | exact dockH_slot driverSlots (by decide) _ _ 0
      | exact dockH_slot driverSlots (by decide) _ _ 1
      | exact dockH_slot driverSlots (by decide) _ _ 2
      | exact (dockH_other driverSlots _ _ _ (by decide)).trans rfl) rfl
  let C := install driverSlots A (C10NativeResidueDriver.output B F F)
  obtain ⟨scalarOut,sr,sw⟩ := C10NativeResidue.signed_run negate p w F (2*B) F bits (decide (z<0)) hw hD hw
  have scaled := sr.pad (fun _=>F)
  have scalarStep := (scaled.dock scalarSlots (by decide) (drivenHead pos out.length) C
    (by intro i; fin_cases i <;> rfl) (by
      intro i; fin_cases i
      all_goals first
        | exact install_slot driverSlots (by decide) _ _ 1
        | exact (install_other driverSlots _ _ _ (by decide)).trans rfl
        | exact (install_other driverSlots _ _ _ (by decide)).trans (congrArg (ZeroPadding.pad F) pbits)
        | exact (install_other driverSlots _ _ _ (by decide)).trans (congrArg (ZeroPadding.pad F) psign)
        | exact (install_other driverSlots _ _ _ (by decide)).trans (pad_replicate_false F 1 (by omega)).symm
        | exact (install_other driverSlots _ _ _ (by decide)).trans (pad_replicate_false F F le_rfl).symm)).congr
          (dockH_existing scalarSlots _ _ (by intro i; fin_cases i <;> rfl)) rfl
  have word := C10NativeSignedResidue.word_eq p w (2*B) bits (C10NativeResidue.signedBit negate (decide (z<0))) hp hpw
  dsimp only at word
  change _=SignedSortKey.binary w (if C10NativeResidue.signedBit negate (decide (z<0)) then
    (p-FinalPrimeRow.horner bits (2*B)%p)%p else FinalPrimeRow.horner bits (2*B)%p) at word
  rw [C10NativeResidueInput.native_horner,C10NativeResidueInput.signed_residue p z.natAbs
    (C10NativeResidue.signedBit negate (decide (z<0))) hp,C10NativeResidue.selected_sign,C10NativeResidueInput.native_sign] at word
  let value := SignedSortKey.binary w (FinalPrimeReduce.intResidue p (if negate then -z else z))
  have vh : value.length=w := SignedSortKey.binary_length _ _
  let D := install scalarSlots C (fun i=>ZeroPadding.pad F (scalarOut i))
  have dword : D 14=ZeroPadding.pad F (frame value) :=
    (install_slot scalarSlots (by decide) _ _ 0).trans
      (congrArg (ZeroPadding.pad F) (sw.trans (congrArg frame word)))
  have dout : D 22=out := (install_other scalarSlots _ _ _ (by decide)).trans
    ((install_other driverSlots _ _ _ (by decide)).trans rfl)
  obtain ⟨copied,cr,cf,_⟩ := CloseoutRowsTouching.FrameStream.copy_run [] value [] out
  have copy : Step CloseoutRowsTouching.FrameStream.machine (2*w+1)
      (![0,out.length] : Fin 2 → ℕ) (![frame value,out] : Fin 2 → List Bool)
      (![2*w+1,out.length+(2*w+1)] : Fin 2 → ℕ)
      (![frame value,out++frame value] : Fin 2 → List Bool) := by
    have h := Step.of_run cr (congrArg Configuration.heads cf) (congrArg Configuration.tapes cf)
    simpa only [CloseoutRowsTouching.FrameStream.cfg,List.nil_append,List.append_nil,List.length_nil,Nat.zero_add,
      List.length_append,frame_length,vh] using h
  have last := (copy.pad (![F,0] : Fin 2 → ℕ)).dock C10NativeResidueAppend.slots (by decide)
    (drivenHead pos out.length) D (by intro i; fin_cases i <;> rfl) (by
      intro i; fin_cases i
      · exact dword
      · exact dout.trans (ZeroPadding.pad_zero out).symm)
  have total := ((first.seq driver).seq scalarStep).seq last
  have time : ((22*B+19+1+(4*B+10))+1+((if negate then 2 else 0)+C10NativeSignedResidue.budget w (2*B)))+1+(2*w+1)=
      coreBudget negate z w := by unfold coreBudget C10NativeResidueAppend.budget C10NativeResidue.budget; dsimp [B]; omega
  rw [time] at total
  refine ⟨_,total,?_,?_⟩
  · exact (install_other C10NativeResidueAppend.slots _ _ _ (by decide)).trans
      ((install_other scalarSlots _ _ _ (by decide)).trans ((install_other driverSlots _ _ _ (by decide)).trans
        ((ZeroPadding.pad_zero _).trans ps)))
  · exact (install_slot C10NativeResidueAppend.slots (by decide) _ _ 1).trans (ZeroPadding.pad_zero _)

def selected (i : Fin 23) : Bool := decide (i≠0 ∧ i≠22)
noncomputable def machine (negate : Bool) := Composition.machine
  (TapeEmbedding.machine 3 (MaskedReset.machine (core negate) selected)) C10NativeResidueRestore.machine
def bank (F w p : ℕ) (source out : List Bool) :=
  C10NativeResidueReuse.extend F w p (C10NativeResidueRestore.canonical F w p source out)

/-- The SAME updated callback returns its own next canonical input. The
four retained templates/logs are physical inputs and persist between calls. -/
theorem run (negate : Bool) (pre tail out : List Bool) (z : ℤ) (p w F : ℕ)
    (hp : 0<p) (hpw : 2*p≤2^w) (hF : coreBudget negate z w+1≤F) :
    Step (machine negate) (2*coreBudget negate z w+2*F+16*w+27)
      (C10NativeResidueReset.head pre.length out.length) (bank F w p (pre++intWord z++tail) out)
      (C10NativeResidueReset.head (pre.length+(intWord z).length) (out.length+(2*w+1)))
      (bank F w p (pre++intWord z++tail)
        (out++frame (SignedSortKey.binary w (FinalPrimeReduce.intResidue p (if negate then -z else z))))) := by
  have capacities : 2*w+2≤F ∧ 4*natBitLength z.natAbs+2≤F ∧
      FinalPrimeResidue.fuel w (2*natBitLength z.natAbs)≤F := by
    unfold coreBudget C10NativeResidueAppend.budget C10NativeResidue.budget C10NativeSignedResidue.budget at hF
    omega
  obtain ⟨hw,hB,hD⟩ := capacities
  obtain ⟨actual,hr,hs,ho⟩ := core_run negate pre tail out z p w F hp hpw hw hB hD
  let pos := pre.length+(intWord z).length
  let len := out.length+(2*w+1)
  let A := C10NativeResidueReuse.extend F w p actual
  have reset := (hr.mask (cap:=F+1) selected (by
    intro i hi; simp only [selected,decide_eq_true_eq] at hi; simp [head,hi.1,hi.2])
    (by omega)).embed (fun _ : Fin 3=>0)
      (![List.replicate F true,frame (SignedSortKey.binary w 0),frame (SignedSortKey.binary w p)] : Fin 3 → List Bool)
  have first : Step (TapeEmbedding.machine 3 (MaskedReset.machine (core negate) selected))
      (2*coreBudget negate z w+2) (C10NativeResidueReset.head pre.length out.length)
      (bank F w p (pre++intWord z++tail) out) (C10NativeResidueReset.head pos len) A := by
    refine (reset.congr_in ?_ ?_).congr ?_ ?_
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [selected,C10NativeResidueReset.head,Fin.addCases]
      · exact (dockH_other C10NativeResidueAppend.slots _ _ _ (by decide)).trans (by simp [pos,drivenHead,head])
      · exact dockH_slot C10NativeResidueAppend.slots (by decide) _ _ 1
    · funext i; fin_cases i <;> rfl
  have lengths : ∀ i,(A (C10NativeResidueRestore.workSlots i)).length≤F := by
    obtain ⟨r,raw,_,rt,steps⟩ := hr
    intro i
    let j : Fin 23 := ⟨i.val+1,by omega⟩
    have hhead : head pre.length out.length j≤0 := by fin_cases i <;> simp [j,head]
    have hinput : (C10NativeResidueRestore.canonical F w p (pre++intWord z++tail) out j).length≤F := by
      fin_cases i <;> simp [j,C10NativeResidueRestore.canonical,ZeroPadding.pad_length,frame_length,SignedSortKey.binary_length] <;> omega
    have bound := C10NativeResidueReset.support_at _ j _ _ r raw F 0 hhead
      (hinput.trans (Nat.le_max_left _ _))
    rw [rt] at bound
    have hi : i.val+1<23 := by omega
    have eq : A (C10NativeResidueRestore.workSlots i)=actual j := by
      simp [A,C10NativeResidueReuse.extend,C10NativeResidueRestore.workSlots,Fin.addCases,hi,j]
    rw [eq]
    exact bound.trans (by omega)
  have ready := C10NativeResidueRestore.restore_run F w p (C10NativeResidueReset.head pos len) A
    (by intro i h0 h22; simp [C10NativeResidueReset.head,h0,h22]) lengths rfl rfl rfl rfl (by omega)
  have last := ready.congr rfl (C10NativeResidueRestore.restored_eq F w p _ _ A hs ho rfl rfl rfl rfl)
  have total := first.seq last
  convert total using 1 <;> first | rfl | omega

end NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidueCallback

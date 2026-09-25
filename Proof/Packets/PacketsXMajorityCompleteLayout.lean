import Proof.Packets.PacketsXMajorityCompleteMeaning
import Proof.Packets.PhysicalRewindInto

/-! Fixed 125-tape majority layout. The complement producer's output is the
enumerator's source, and the enumerator's output is the parity source. The
unused source ports are empty; no derived polynomial bank is an input. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NormalizedFiniteTransport Theorem25Completion.CycleBounds PairedPacketMeaning
noncomputable section

def assemble {α : Type} (a : Fin 39→α) (b : Fin 47→α) (c : Fin 38→α) (spare : α) : Fin 125→α :=
  Fin.addCases (m:=39) (n:=86) (motive:=fun _=>α) a
    (Fin.addCases (m:=47) (n:=39) (motive:=fun _=>α) b
      (Fin.addCases (m:=38) (n:=1) (motive:=fun _=>α) c (fun _=>spare)))
def enumBase (i : Fin 47) : Fin 125 := ⟨39+i.val,by omega⟩
def foldBase (i : Fin 38) : Fin 125 := ⟨86+i.val,by omega⟩
def enumSlots (i : Fin 47) : Fin 125 := if i=34 then 37 else enumBase i
def foldSlots (i : Fin 38) : Fin 125 := if i=34 then 82 else foldBase i

theorem enum_injective : Function.Injective enumSlots := by
  intro i j h
  by_cases hi : i=34 <;>by_cases hj : j=34
  · exact hi.trans hj.symm
  · simp only [enumSlots,if_pos hi,if_neg hj] at h
    have hv:=congrArg Fin.val h
    dsimp only [enumBase] at hv
    omega
  · simp only [enumSlots,if_neg hi,if_pos hj] at h
    have hv:=congrArg Fin.val h
    dsimp only [enumBase] at hv
    omega
  · simp only [enumSlots,if_neg hi,if_neg hj] at h
    apply Fin.ext
    have hv:=congrArg Fin.val h
    dsimp only [enumBase] at hv
    omega

theorem fold_injective : Function.Injective foldSlots := by
  intro i j h
  by_cases hi : i=34 <;>by_cases hj : j=34
  · exact hi.trans hj.symm
  · simp only [foldSlots,if_pos hi,if_neg hj] at h
    have hv:=congrArg Fin.val h
    dsimp only [foldBase] at hv
    omega
  · simp only [foldSlots,if_neg hi,if_pos hj] at h
    have hv:=congrArg Fin.val h
    dsimp only [foldBase] at hv
    omega
  · simp only [foldSlots,if_neg hi,if_neg hj] at h
    apply Fin.ext
    have hv:=congrArg Fin.val h
    dsimp only [foldBase] at hv
    omega

theorem enum_below (i : Fin 47) : (enumSlots i).val<86 := by
  by_cases hi : i=34
  · simp [enumSlots,hi]
  · simp only [enumSlots,if_neg hi,enumBase]
    omega
theorem fold_other (j : Fin 38) (hj : j≠34) : ∀i,enumSlots i≠foldSlots j := by
  intro i he
  have hi:=enum_below i
  have hv:=congrArg Fin.val he
  simp only [foldSlots,if_neg hj,foldBase] at hv
  omega

theorem assemble_fold {α : Type} (a : Fin 39→α) (b : Fin 47→α)
    (c : Fin 38→α) (spare : α) (i : Fin 38) :
    assemble a b c spare (foldBase i)=c i := by
  fin_cases i <;>rfl

def compH (out : List Bool) : Fin 39→Nat :=
  Fin.addCases (m:=38) (n:=1) (motive:=fun _=>Nat) (ComplementPacketStep.H out) (fun _=>1)
def compA (C R : Nat) (ps : List Poly) (index : Nat) (right : Poly) (out : List Bool) : Fin 39→List Bool :=
  Fin.addCases (m:=38) (n:=1) (motive:=fun _=>List Bool)
    (ComplementPacketStep.A C R index right ps out) (fun _=>CompareMachine.word ps.length)
def enumCold (C R : Nat) (ps : List Poly) := Function.update (enumerationA C R ps 0 []) 34 []
def foldCold (C R N : Nat) := OrderedPacketFold.tapes C R N N [] [] []
def inputH : Fin 125→Nat := assemble (compH []) (enumerationH []) OrderedPacketFold.H 1
def input (C R : Nat) (ps : List Poly) : Fin 125→List Bool :=
  assemble (compA C R ps 0 [] []) (enumCold C R ps) (foldCold C R (2^ps.length))
    (UnaryTemplate.tape (R^2))
def paired (C R : Nat) (ps : List Poly) := OrderedPacketStep.bank C R (ComplementPacketBank.pairs ps)
def producedH (C R : Nat) (ps : List Poly) : Fin 125→Nat :=
  assemble (compH (paired C R ps)) (enumerationH []) OrderedPacketFold.H 1
def produced (C R : Nat) (ps : List Poly) : Fin 125→List Bool :=
  assemble (compA C R ps ps.length (ComplementPacketBank.prior ps [] ps.length) (paired C R ps))
    (enumCold C R ps) (foldCold C R (2^ps.length)) (UnaryTemplate.tape (R^2))
def pairedReadyH (C R : Nat) (ps : List Poly) := Function.update (producedH C R ps) 37 0
def termBank (C R : Nat) (ps : List Poly) := OrderedPacketStep.bank C R (terms ps)
def enumeratedH (C R : Nat) (ps : List Poly) :=
  dockH enumSlots (pairedReadyH C R ps) (enumerationH (termBank C R ps))
def enumerated (C R : Nat) (ps : List Poly) :=
  install enumSlots (produced C R ps) (enumerationA C R ps (2^ps.length-1) (termBank C R ps))
def foldReadyH (C R : Nat) (ps : List Poly) := Function.update (enumeratedH C R ps) 82 0
def finalH (C R : Nat) (ps : List Poly) := dockH foldSlots (foldReadyH C R ps) OrderedPacketFold.H
def final (C R : Nat) (ps : List Poly) :=
  install foldSlots (enumerated C R ps)
    (OrderedPacketFold.tapes C R 0 (2^ps.length)
      (OrderedPacketFold.last (terms ps) [] (2^ps.length)) (majority ps) (terms ps))

theorem enum_entry_heads (C R : Nat) (ps : List Poly) (j : Fin 47) :
    pairedReadyH C R ps (enumSlots j)=enumerationH [] j := by
  fin_cases j <;>rfl
theorem enum_entry_tapes (C R : Nat) (ps : List Poly) (j : Fin 47) :
    produced C R ps (enumSlots j)=enumerationA C R ps 0 [] j := by
  fin_cases j <;>rfl

theorem fold_entry_heads (C R : Nat) (ps : List Poly) (j : Fin 38) :
    foldReadyH C R ps (foldSlots j)=OrderedPacketFold.H j := by
  by_cases hj : j=34
  · subst j;rfl
  · have h82 : foldSlots j≠82 := by
      intro he
      have hv:=congrArg Fin.val he
      simp only [foldSlots,if_neg hj,foldBase] at hv
      omega
    rw [foldReadyH,Function.update_of_ne h82,enumeratedH,
      dockH_other enumSlots _ _ _ (fold_other j hj)]
    have h37 : foldSlots j≠37 := by
      intro he
      have hv:=congrArg Fin.val he
      simp only [foldSlots,if_neg hj,foldBase] at hv
      omega
    rw [pairedReadyH,Function.update_of_ne h37]
    simp only [producedH,foldSlots,if_neg hj,assemble_fold]

theorem fold_entry_tapes (C R : Nat) (ps : List Poly) (j : Fin 38) :
    enumerated C R ps (foldSlots j)=
      OrderedPacketFold.tapes C R (2^ps.length) (2^ps.length) [] [] (terms ps) j := by
  by_cases hj : j=34
  · subst j
    change install enumSlots (produced C R ps) _ (enumSlots 43)=_
    rw [install_slot enumSlots enum_injective]
    rfl
  · rw [enumerated,install_other enumSlots _ _ _ (fold_other j hj)]
    simp only [produced,foldSlots,if_neg hj,assemble_fold]
    fin_cases j <;>first
      | exact False.elim (hj rfl)
      | rfl

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete

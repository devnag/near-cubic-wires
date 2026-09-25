import Proof.CaseAnalysis.RowsModeWindowGuard
import Proof.CaseAnalysis.RowsModeWindowSelect

/-! The elementary and scalar banks share one paid log. Subset digit width
v remains separate from coefficient width u, and original M is retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowLayout
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey ExtDecompositionBatch
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scalarCaps (C : Nat) (i : Fin 8):=if i=5 then 0 else C
def scalars (u offset b scratch degree target C : Nat) (nonzero guard : Bool) : Fin 8→List Bool:=
  fun i=>ZeroPadding.pad (scalarCaps C i)
    (CloseoutRowsModeWindowGuard.data u offset b scratch degree target (C+1) nonzero guard i)
def extra (u M offset b scratch degree target C : Nat) (nonzero guard : Bool) : Fin 8→List Bool:=
  let A:=scalars u offset b scratch degree target C nonzero guard
  ![A 0,A 1,A 2,A 3,A 4,A 6,A 7,List.replicate M true]
def heads (out : List Bool) : Fin 60→Nat:=Fin.addCases (m:=52) (n:=8) (motive:=fun _=>Nat)
  (CloseoutRowsModeElementaryLayout.heads out) (fun _=>0)
noncomputable def data (v u M a offset b scratch degree target C : Nat)
    (nonzero guard : Bool) (out : List Bool) : Fin 60→List Bool:=
  Fin.addCases (m:=52) (n:=8) (motive:=fun _=>List Bool)
    (CloseoutRowsModeElementaryReusable.paddedBlank v a M C out)
    (extra u M offset b scratch degree target C nonzero guard)
def guardSlots : Fin 8→Fin 60:=![52,53,54,55,56,51,57,58]

theorem guard_slot (v u M a offset b scratch degree target C : Nat)
    (nonzero guard : Bool) (out : List Bool) (i : Fin 8) :
    data v u M a offset b scratch degree target C nonzero guard out (guardSlots i)=
      scalars u offset b scratch degree target C nonzero guard i:=by
  fin_cases i <;> rfl

theorem degree_read (v u M a offset b scratch degree target C : Nat)
    (nonzero guard : Bool) (out : List Bool) :
    readTapeBit (data v u M a offset b scratch degree target C nonzero guard out 48) 1=decide (0<a):=by
  change readTapeBit (CloseoutRowsModeElementaryReusable.paddedBlank v a M C out 48) 1=_
  simp only [CloseoutRowsModeElementaryReusable.paddedBlank,ZeroPadding.read_pad,
    CloseoutRowsModeElementaryLayout.blank_eq]
  change readTapeBit (CompareMachine.word a) 1=_
  cases a <;> simp [CompareMachine.word,readTapeBit,List.getD,List.replicate_succ]

theorem guard_read (v u M a offset b scratch degree target C : Nat)
    (nonzero guard : Bool) (out : List Bool) :
    readTapeBit (data v u M a offset b scratch degree target C nonzero guard out 56) 0=guard:=by
  change readTapeBit (ZeroPadding.pad C [guard]) 0=guard
  rw [ZeroPadding.read_pad]
  rfl

theorem population_read (v u M a offset b scratch degree target C : Nat)
    (nonzero guard : Bool) (out : List Bool) :
    readTapeBit (data v u M a offset b scratch degree target C nonzero guard out 59) 0=decide (0<M):=by
  change readTapeBit (List.replicate M true) 0=_
  cases M <;> simp [readTapeBit,List.getD,List.replicate_succ]

theorem select_run (v u M a offset b scratch degree target C : Nat)
    (nonzero guard : Bool) (out : List Bool) :
    ∃ r,runFrom CloseoutRowsModeWindowSelect.machine 2
      ⟨CloseoutRowsModeWindowSelect.machine.start,heads out,
        data v u M a offset b scratch degree target C nonzero guard out⟩=some r ∧
      r.final=⟨CloseoutRowsModeWindowSelect.result guard (decide (0<M)) (decide (0<a)),heads out,
        data v u M a offset b scratch degree target C nonzero guard out⟩ ∧ r.steps=2:=
  CloseoutRowsModeWindowSelect.selected_run _ _ _ _ _ (by rfl) (by rfl) (by rfl)
    (degree_read _ _ _ _ _ _ _ _ _ _ _ _ _) (guard_read _ _ _ _ _ _ _ _ _ _ _ _ _)
    (population_read _ _ _ _ _ _ _ _ _ _ _ _ _)

noncomputable def elementary:=TapeEmbedding.machine 8 CloseoutRowsModeElementaryReusable.machine

theorem elementary_run (v u M a offset b scratch degree target C : Nat)
    (nonzero guard : Bool) (out : List Bool) (hM : 0<M) (hMv : M≤2^v)
    (hmeta : 2*v+a+3≤C) (hC : CloseoutRowsModeElementary.budget v a M+1≤C) :
    Step elementary (CloseoutRowsModeElementaryReusable.budget v a M C) (heads out)
      (data v u M a offset b scratch degree target C nonzero guard out)
      (heads (out++CloseoutRowsModeElementary.bodyWord v a M))
      (data v u M a offset b scratch degree target C nonzero guard (out++CloseoutRowsModeElementary.bodyWord v a M)):=
  (CloseoutRowsModeElementaryReusable.padded_run v a M C out hM hMv hmeta hC).embed
    (fun _ : Fin 8=>0) (extra u M offset b scratch degree target C nonzero guard)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowLayout

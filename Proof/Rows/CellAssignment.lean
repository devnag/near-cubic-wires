import Proof.Rows.Plan

/-! Paid conversion of the two resident half-cube cursors into the assignment
order consumed by the printer. Row bits precede column bits, including odd
residual arities. Both cursor frames and the zero counter are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_CellAssignment
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.CloseoutFinal
noncomputable section

def slots (side : Fin 2) : Fin 3→Fin 4 := ![side.castLE (by omega),2,3]
theorem slots_injective (side : Fin 2) : Function.Injective (slots side) := by
  intro i j h
  have hv:=congrArg Fin.val h
  fin_cases side <;> fin_cases i <;> fin_cases j <;> simp [slots] at hv ⊢
theorem pick_slots (side : Fin 2) (i : Fin 4) : RecoveryFocus.pick (slots side) i =
    if i.val=side.val then some 0 else if i=2 then some 1
    else if i=3 then some 2 else none := by
  fin_cases side <;> fin_cases i <;> first
    | exact RecoveryFocus.pick_slot _ (slots_injective _) 0
    | exact RecoveryFocus.pick_slot _ (slots_injective _) 1
    | exact RecoveryFocus.pick_slot _ (slots_injective _) 2
    | decide

def heads (out : List Bool) : Fin 4→Nat := ![0,0,out.length,0]
def bank (rows cols out : List Bool) (C : Nat) : Fin 4→List Bool :=
  ![frame rows,frame cols,out,List.replicate C false]
def append (side : Fin 2) := RecoveryFocus.machine (slots side) CompetitorRawScalarEmit.machine
def raw := Composition.machine (append 0) (append 1)
def selected (i : Fin 4) : Bool := decide (i=2)
def machine := MaskedReset.machine raw selected
def data (rows cols out : List Bool) (C D : Nat) : Fin 5→List Bool :=
  ![frame rows,frame cols,out,List.replicate C false,List.replicate D false]

theorem append_run (side : Fin 2) (rows cols out : List Bool) (C : Nat)
    (hC : 2*(if side=0 then rows else cols).length+1≤C) :
    let bits := if side=0 then rows else cols
    Step (append side) (4*bits.length+3) (heads out) (bank rows cols out C)
      (heads (out++bits)) (bank rows cols (out++bits) C) := by
  obtain ⟨r,hr,hf,_⟩ := CompetitorRawScalarAppend.raw_append_run
    (if side=0 then rows else cols) out C hC
  have base:=Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  have h:=base.dock (slots side) (slots_injective side) (heads out) (bank rows cols out C)
    (by intro i;fin_cases side <;> fin_cases i <;> rfl)
    (by intro i;fin_cases side <;> fin_cases i <;> rfl)
  apply h.congr
  · funext i;fin_cases side <;> fin_cases i <;>
      simp [dockH,pick_slots,heads,CompetitorRawScalarAppend.cfg]
  · funext i;fin_cases side <;> fin_cases i <;>
      simp [install,pick_slots,bank,CompetitorRawScalarAppend.cfg]

theorem raw_run (rows cols : List Bool) (C : Nat)
    (hr : 2*rows.length+1≤C) (hc : 2*cols.length+1≤C) :
    Step raw (4*(rows.length+cols.length)+7) (fun _=>0) (bank rows cols [] C)
      (heads (rows++cols)) (bank rows cols (rows++cols) C) := by
  have h := (append_run 0 rows cols [] C hr).seq (append_run 1 rows cols rows C hc)
  simp only [if_true,show (1 : Fin 2)≠0 from by decide,if_false] at h
  rw [show (4*rows.length+3)+1+(4*cols.length+3)=4*(rows.length+cols.length)+7 by omega] at h
  exact h.congr_in (by funext i;fin_cases i <;>rfl) rfl

theorem run (rows cols : List Bool) (C D : Nat)
    (hr : 2*rows.length+1≤C) (hc : 2*cols.length+1≤C)
    (hD : 4*(rows.length+cols.length)+7≤D) :
    Step machine (8*(rows.length+cols.length)+16) (fun _=>0) (data rows cols [] C D)
      (fun _=>0) (data rows cols (rows++cols) C D) := by
  have h := (raw_run rows cols C hr hc).mask selected (by intros;rfl) hD
  rw [show 2*(4*(rows.length+cols.length)+7)+2=8*(rows.length+cols.length)+16 by omega] at h
  refine (h.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i <;>rfl

theorem run_padded (rows cols : List Bool) (C D : Nat)
    (hr : 2*rows.length+1≤C) (hc : 2*cols.length+1≤C)
    (hD : 4*(rows.length+cols.length)+7≤D) :
    Step machine (8*(rows.length+cols.length)+16) (fun _=>0)
      (data rows cols (List.replicate (rows.length+cols.length) false) C D)
      (fun _=>0) (data rows cols (rows++cols) C D) := by
  have h := (run rows cols C D hr hc hD).pad (![0,0,rows.length+cols.length,0,0] : Fin 5→Nat)
  refine (h.congr_in rfl ?_).congr rfl ?_
  all_goals funext i;fin_cases i <;> simp [data,ZeroPadding.pad]

theorem halfPoint_word (l r rowN colN : Nat) :
    SignedSortKey.binary l rowN++SignedSortKey.binary r colN =
      List.ofFn (C10SupplierRowInput.halfPoint l r rowN colN) := by
  rw [←RepairSource.VerifierDecoding.fixedBits_binary l rowN,
    ←RepairSource.VerifierDecoding.fixedBits_binary r colN]
  exact (List.ofFn_fin_append _ _).symm

end
end PCJ45bee56da9f34d5a_CellAssignment

import Proof.Rows.CellAssignment

/-! The first actual cell join: decode both resident framed half-cursors,
then scatter the concatenated external assignment over its resident mask.
Every input tape and cursor is retained, with explicit reusable zero logs. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_CellScatter
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.P1Closure NearCubicWires.SupplierEstimator
noncomputable section

def decodeSlots : Fin 5→Fin 8 := ![0,1,2,3,4]
def scatterSlots : Fin 5→Fin 8 := ![5,2,6,7,4]
theorem decode_injective : Function.Injective decodeSlots := by decide
theorem scatter_injective : Function.Injective scatterSlots := by decide
theorem pick_decode (i : Fin 8) : RecoveryFocus.pick decodeSlots i =
    if i=0 then some 0 else if i=1 then some 1 else if i=2 then some 2
    else if i=3 then some 3 else if i=4 then some 4 else none := by
  fin_cases i <;> first
    | exact RecoveryFocus.pick_slot _ decode_injective 0
    | exact RecoveryFocus.pick_slot _ decode_injective 1
    | exact RecoveryFocus.pick_slot _ decode_injective 2
    | exact RecoveryFocus.pick_slot _ decode_injective 3
    | exact RecoveryFocus.pick_slot _ decode_injective 4
    | decide
theorem pick_scatter (i : Fin 8) : RecoveryFocus.pick scatterSlots i =
    if i=5 then some 0 else if i=2 then some 1 else if i=6 then some 2
    else if i=7 then some 3 else if i=4 then some 4 else none := by
  fin_cases i <;> first
    | exact RecoveryFocus.pick_slot _ scatter_injective 0
    | exact RecoveryFocus.pick_slot _ scatter_injective 1
    | exact RecoveryFocus.pick_slot _ scatter_injective 2
    | exact RecoveryFocus.pick_slot _ scatter_injective 3
    | exact RecoveryFocus.pick_slot _ scatter_injective 4
    | decide

def heads : Fin 8→Nat := ![0,0,0,0,0,0,0,1]
def bank (rows cols bits output member : List Bool) (q C D : Nat) : Fin 8→List Bool :=
  ![frame rows,frame cols,bits,List.replicate C false,List.replicate D false,
    member,output,CompareMachine.word q]
def decode := RecoveryFocus.machine decodeSlots PCJ45bee56da9f34d5a_CellAssignment.machine
def scatter := RecoveryFocus.machine scatterSlots FrozenMask.readyMachine
def machine := Composition.machine decode scatter

theorem decode_run (rows cols output member : List Bool) (q C D : Nat)
    (hr : 2*rows.length+1≤C) (hc : 2*cols.length+1≤C)
    (hD : 4*(rows.length+cols.length)+7≤D) :
    Step decode (8*(rows.length+cols.length)+16) heads
      (bank rows cols (List.replicate (rows.length+cols.length) false) output member q C D)
      heads (bank rows cols (rows++cols) output member q C D) := by
  have h := (PCJ45bee56da9f34d5a_CellAssignment.run_padded rows cols C D hr hc hD).dock
    decodeSlots decode_injective heads
      (bank rows cols (List.replicate (rows.length+cols.length) false) output member q C D)
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
  apply h.congr
  · funext i;fin_cases i <;>simp [dockH,pick_decode,heads]
  · funext i;fin_cases i <;>simp [install,pick_decode,bank,PCJ45bee56da9f34d5a_CellAssignment.data]

theorem scatter_run {q : Nat} (live : Finset (Fin q)) (y : BitInput live.card)
    (rows cols : List Bool) (C D : Nat) (hD : 4*q+3≤D) :
    Step scatter (8*q+8) heads
      (bank rows cols (List.ofFn y) (List.replicate q false)
        (CloseoutRowsGateSupport.gateMembers live) q C D)
      heads (bank rows cols (List.ofFn y)
        (List.ofFn (C10NaturalHardwireScore.frozenMask live y))
        (CloseoutRowsGateSupport.gateMembers live) q C D) := by
  have hp := (FrozenMask.ready_run live y D hD).pad (![0,0,q,0,0] : Fin 5→Nat)
  have base : Step FrozenMask.readyMachine (8*q+8) (![0,0,0,1,0] : Fin 5→Nat)
      ![CloseoutRowsGateSupport.gateMembers live,List.ofFn y,List.replicate q false,
        CompareMachine.word q,List.replicate D false]
      (![0,0,0,1,0] : Fin 5→Nat)
      ![CloseoutRowsGateSupport.gateMembers live,List.ofFn y,
        List.ofFn (C10NaturalHardwireScore.frozenMask live y),
        CompareMachine.word q,List.replicate D false] := by
    refine (hp.congr_in rfl ?_).congr rfl ?_
    all_goals funext i;fin_cases i <;>simp [ZeroPadding.pad]
  have h := base.dock scatterSlots scatter_injective heads
    (bank rows cols (List.ofFn y) (List.replicate q false)
      (CloseoutRowsGateSupport.gateMembers live) q C D)
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
  apply h.congr
  · funext i;fin_cases i <;>simp [dockH,pick_scatter,heads]
  · funext i;fin_cases i <;>simp [install,pick_scatter,bank]

theorem run {q : Nat} (live : Finset (Fin q)) (y : BitInput live.card)
    (rows cols : List Bool) (C D : Nat) (hword : rows++cols=List.ofFn y)
    (hr : 2*rows.length+1≤C) (hc : 2*cols.length+1≤C)
    (hD : 4*(rows.length+cols.length)+7≤D) (hQ : 4*q+3≤D) :
    Step machine (8*(rows.length+cols.length)+8*q+25) heads
      (bank rows cols (List.replicate (rows.length+cols.length) false) (List.replicate q false)
        (CloseoutRowsGateSupport.gateMembers live) q C D)
      heads (bank rows cols (List.ofFn y)
        (List.ofFn (C10NaturalHardwireScore.frozenMask live y))
        (CloseoutRowsGateSupport.gateMembers live) q C D) := by
  have first := decode_run rows cols (List.replicate q false)
    (CloseoutRowsGateSupport.gateMembers live) q C D hr hc hD
  rw [hword] at first
  have h := first.seq (scatter_run live y rows cols C D hQ)
  rw [show (8*(rows.length+cols.length)+16)+1+(8*q+8)=
    8*(rows.length+cols.length)+8*q+25 by omega] at h
  exact h

theorem frozenMask_compl {q : Nat} (live : Finset (Fin q)) (y : BitInput liveᶜ.card) :
    C10NaturalHardwireScore.frozenMask liveᶜ y=C10SupplierRowInput.joinInput live (fun _=>false) y := by
  funext i
  obtain ⟨side,rfl⟩ := (normalizedLiveExternalCoordinateEquiv live).surjective i
  cases side with
  | inl j =>
    rw [C10SupplierRowInput.joinInput_coord]
    apply FrozenMask.false_outside
    simpa only [normalizedLiveExternalCoordinateEquiv,finSumEquivOfFinset_inl,
      Finset.mem_compl,not_not] using Finset.orderEmbOfFin_mem live rfl j
  | inr j =>
    rw [C10SupplierRowInput.joinInput_coord]
    exact C10SupplierRowInput.joinInput_coord liveᶜ y (fun _=>false) (Sum.inl j)

/-- The physical assignment is the paper's exact printerPoint, for both parities. -/
theorem cursor_run {q : Nat} (live : Finset (Fin q)) (s : Nat)
    (ha : (s+1)/2+s/2=liveᶜ.card) (rowN colN C D : Nat)
    (hl : 2*((s+1)/2)+1≤C) (hr : 2*(s/2)+1≤C)
    (hD : 4*((s+1)/2+s/2)+7≤D) (hQ : 4*q+3≤D) :
    let rows:=SignedSortKey.binary ((s+1)/2) rowN
    let cols:=SignedSortKey.binary (s/2) colN
    let point:=C10ExternalRowLoop.printerPoint live s ha rowN colN
    Step machine (8*((s+1)/2+s/2)+8*q+25) heads
      (bank rows cols (List.replicate ((s+1)/2+s/2) false) (List.replicate q false)
        (CloseoutRowsGateSupport.gateMembers liveᶜ) q C D)
      heads (bank rows cols (List.ofFn point)
        (List.ofFn (C10SupplierRowInput.joinInput live (fun _=>false) point))
        (CloseoutRowsGateSupport.gateMembers liveᶜ) q C D) := by
  have word : SignedSortKey.binary ((s+1)/2) rowN++SignedSortKey.binary (s/2) colN=
      List.ofFn (C10ExternalRowLoop.printerPoint live s ha rowN colN) :=
    (PCJ45bee56da9f34d5a_CellAssignment.halfPoint_word _ _ _ _).trans
      (List.ofFn_congr ha _)
  have h:=run liveᶜ (C10ExternalRowLoop.printerPoint live s ha rowN colN)
    (SignedSortKey.binary ((s+1)/2) rowN) (SignedSortKey.binary (s/2) colN) C D word
    (by simpa using hl) (by simpa using hr) (by simpa using hD) hQ
  simpa only [SignedSortKey.binary_length,frozenMask_compl] using h

end
end PCJ45bee56da9f34d5a_CellScatter

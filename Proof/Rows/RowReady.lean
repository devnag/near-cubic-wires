import Proof.Rows.RowClear

/-!
# `Core.completeReady`, reduced to the completion machine

Everything in `Plan.Core.completeReady` except the `Step complete` itself and the single
`Row.budget ≤ rowFuel` inequality is discharged here from the chosen `state`:

* `prepareFuel=0` and both entry equalities are definitional;
* the framing capacity premise IS `RowCaps.Good`'s second clause;
* the cleanup certificate is `PCJ45bee56da9f34d5a_RowClear.clearBank`, and `2*cap+4` is the
  chosen `cleanupFuel` on the nose.

`ready_body` therefore states exactly what is still owed at this node.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ45bee56da9f34d5a_RowReady
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.P1Closure
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJ45bee56da9f34d5a_RowState PCJ45bee56da9f34d5a_RowClear
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

variable (printer : WilliamsAlgorithm) (work : Nat) {q Lq : Nat}
  (a : DecompositionAlgorithm) (F : Packets.Family q Lq) (g : Packets.Geometry F)
  (layout : Packets.Layout a F g)
  (facts : ∀ r ∈ F.rows, Packets.PacketFacts a F g r)
  (caps : RowCaps) (reserve : Fin 440 → Nat) (baseBank : Nat → Fin (rowWork work) → List Bool) (drv lg : Fin (rowWork work))
  (completeStates : Nat) (complete : Machine (rowTapes printer work) completeStates)
  (completeFuel rowFuel : Nat) (j : Fin F.rows.attach.length) (out : List Bool)

/-- The Core's program, at the chosen cleanup slots. -/
def prog := PCJ45bee56da9f34d5a_Plan.program (clearSlots printer work drv lg) complete

/-- The Core's state. -/
def stt := rowState printer work a F g layout caps reserve baseBank drv lg completeFuel rowFuel

/-- The banks of row `j`, as `Family.rowBanks` reads them out of that state. -/
def bnk := PCJ38fbfed565f64139_Family.rowBanks printer a F g layout facts
  (stt printer work a F g layout caps reserve baseBank drv lg completeFuel rowFuel) j.val out

/-- The row this index names, and its datum. -/
abbrev rw := PCJ38fbfed565f64139_Family.rowAt F j

theorem exit_word :
    out++PCJ38fbfed565f64139_Family.emit printer a F g layout facts j.val=
      out++(Packets.datum a F g layout (rw F j).val (rw F j).property
        (facts (rw F j).val (rw F j).property)).word printer := by
  rw [PCJ38fbfed565f64139_Family.word_at]
  rfl

/-- **The cleanup certificate at the actual row banks.** -/
def cleanup (hne : drv≠lg)
    (hcap : ∀ i,2*(PCJ38fbfed565f64139_Row.Frame.fields printer
      (Packets.datum a F g layout (rw F j).val (rw F j).property
        (facts (rw F j).val (rw F j).property)) i).length+1≤caps.copyCap) :
    PCJ45bee56da9f34d5a_Plan.ClearBank (clearSlots printer work drv lg)
      (PCJ38fbfed565f64139_Row.frameOutH printer
        (PCJ38fbfed565f64139_Ready.code
          (prog printer work drv lg completeStates complete)) a F g layout
        (rw F j).val (rw F j).property (facts (rw F j).val (rw F j).property)
        (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out) out)
      (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out).exitH
      (PCJ38fbfed565f64139_Row.frameOutA printer
        (PCJ38fbfed565f64139_Ready.code
          (prog printer work drv lg completeStates complete)) a F g layout
        (rw F j).val (rw F j).property (facts (rw F j).val (rw F j).property)
        (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out) out)
      (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out).exitA :=
  clearBank printer work caps drv lg a F g layout reserve baseBank (rw F j).val (rw F j).property
    (facts (rw F j).val (rw F j).property)
    (PCJ38fbfed565f64139_Ready.code (prog printer work drv lg completeStates complete))
    (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out)
    j.val out rfl rfl rfl rfl rfl rfl
    (congrArg (headBank printer work a F g (j.val+1))
      (exit_word printer a F g layout facts j out))
    (congrArg (bank printer work a F g layout caps reserve baseBank drv lg (j.val+1))
      (exit_word printer a F g layout facts j out)) hne hcap

/-- **`Core.completeReady`'s body, reduced.**  Only the completion `Step` and the single row
cost inequality remain hypotheses; the five bank obligations are closed. -/
theorem ready_body (hne : drv≠lg)
    (hcap : ∀ i,2*(PCJ38fbfed565f64139_Row.Frame.fields printer
      (Packets.datum a F g layout (rw F j).val (rw F j).property
        (facts (rw F j).val (rw F j).property)) i).length+1≤caps.copyCap)
    (hstep : Step complete completeFuel
      (PCJ38fbfed565f64139_Row.headerOutH printer
        (PCJ38fbfed565f64139_Ready.code (prog printer work drv lg completeStates complete))
        a F g layout (rw F j).val
        (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out)
        (PCJ38fbfed565f64139_Family.rawBefore a F g j.val)
        (PCJ38fbfed565f64139_Family.rawAfter a F g j.val))
      (PCJ38fbfed565f64139_Row.headerOutA printer
        (PCJ38fbfed565f64139_Ready.code (prog printer work drv lg completeStates complete))
        a F g layout (rw F j).val
        (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out)
        (PCJ38fbfed565f64139_Family.rawBefore a F g j.val)
        (PCJ38fbfed565f64139_Family.rawAfter a F g j.val))
      (PCJ38fbfed565f64139_Row.frameInH printer
        (PCJ38fbfed565f64139_Ready.code (prog printer work drv lg completeStates complete))
        (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out) out)
      (PCJ38fbfed565f64139_Row.frameInA printer
        (PCJ38fbfed565f64139_Ready.code (prog printer work drv lg completeStates complete))
        a F g layout (rw F j).val (rw F j).property (facts (rw F j).val (rw F j).property)
        (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out) out))
    (hbud : PCJ38fbfed565f64139_Row.budget printer a F g layout (rw F j).val (rw F j).property
      (facts (rw F j).val (rw F j).property)
      (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out)≤
      rowFuel) :
    (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out).prepareFuel=0 ∧
    (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out).entryH=
      PCJ38fbfed565f64139_Row.headerInH printer
        (PCJ38fbfed565f64139_Ready.code (prog printer work drv lg completeStates complete))
        (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out)
        (PCJ38fbfed565f64139_Family.rawBefore a F g j.val) ∧
    (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out).entryA=
      PCJ38fbfed565f64139_Row.headerInA printer
        (PCJ38fbfed565f64139_Ready.code (prog printer work drv lg completeStates complete))
        a F g layout (rw F j).val
        (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out)
        (PCJ38fbfed565f64139_Family.rawBefore a F g j.val)
        (PCJ38fbfed565f64139_Family.rawAfter a F g j.val) ∧
    (∀ i,2*(PCJ38fbfed565f64139_Row.Frame.fields printer
      (Packets.datum a F g layout (rw F j).val (rw F j).property
        (facts (rw F j).val (rw F j).property)) i).length+1≤
      (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out).copyCap) ∧
    Step complete
      (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out).completeFuel
      (PCJ38fbfed565f64139_Row.headerOutH printer
        (PCJ38fbfed565f64139_Ready.code (prog printer work drv lg completeStates complete))
        a F g layout (rw F j).val
        (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out)
        (PCJ38fbfed565f64139_Family.rawBefore a F g j.val)
        (PCJ38fbfed565f64139_Family.rawAfter a F g j.val))
      (PCJ38fbfed565f64139_Row.headerOutA printer
        (PCJ38fbfed565f64139_Ready.code (prog printer work drv lg completeStates complete))
        a F g layout (rw F j).val
        (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out)
        (PCJ38fbfed565f64139_Family.rawBefore a F g j.val)
        (PCJ38fbfed565f64139_Family.rawAfter a F g j.val))
      (PCJ38fbfed565f64139_Row.frameInH printer
        (PCJ38fbfed565f64139_Ready.code (prog printer work drv lg completeStates complete))
        (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out) out)
      (PCJ38fbfed565f64139_Row.frameInA printer
        (PCJ38fbfed565f64139_Ready.code (prog printer work drv lg completeStates complete))
        a F g layout (rw F j).val (rw F j).property (facts (rw F j).val (rw F j).property)
        (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out) out) ∧
    ∃ clear : PCJ45bee56da9f34d5a_Plan.ClearBank (clearSlots printer work drv lg)
      (PCJ38fbfed565f64139_Row.frameOutH printer
        (PCJ38fbfed565f64139_Ready.code (prog printer work drv lg completeStates complete))
        a F g layout (rw F j).val (rw F j).property (facts (rw F j).val (rw F j).property)
        (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out) out)
      (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out).exitH
      (PCJ38fbfed565f64139_Row.frameOutA printer
        (PCJ38fbfed565f64139_Ready.code (prog printer work drv lg completeStates complete))
        a F g layout (rw F j).val (rw F j).property (facts (rw F j).val (rw F j).property)
        (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out) out)
      (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out).exitA,
      2*clear.cap+4≤
        (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out).cleanupFuel ∧
      PCJ38fbfed565f64139_Row.budget printer a F g layout (rw F j).val (rw F j).property
        (facts (rw F j).val (rw F j).property)
        (bnk printer work a F g layout facts caps reserve baseBank drv lg completeFuel rowFuel j out)≤
        rowFuel :=
  ⟨rfl,
   entry_heads printer work a F g
     (PCJ45bee56da9f34d5a_Plan.program (clearSlots printer work drv lg) complete) j.val out,
   entry_tapes printer work a F g layout caps reserve baseBank drv lg
     (PCJ45bee56da9f34d5a_Plan.program (clearSlots printer work drv lg) complete) j out,
   hcap,hstep,
   ⟨cleanup printer work a F g layout facts caps reserve baseBank drv lg completeStates complete
      completeFuel rowFuel j out hne hcap,Nat.le_refl _,hbud⟩⟩

end
end PCJ45bee56da9f34d5a_RowReady

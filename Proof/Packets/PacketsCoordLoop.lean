import Proof.Packets.PacketsCoordCellStage
import Proof.MachineModel.BlockScrubEntry

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.Residual
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.BlockPlatform
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
noncomputable section

variable {a : DecompositionAlgorithm}

theorem flatMap_range_getD {α β : Type} (f : α → List β) (d : α) : ∀ l : List α,
    (List.range l.length).flatMap (fun j => f (l.getD j d)) = (l.map f).flatten
  | [] => rfl
  | x :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.map_cons, List.flatten_cons]
    congr 1
    rw [List.flatMap_map]
    exact flatMap_range_getD f d l

/-- The concatenated per-mask vectors are the coordinate word. -/
theorem vecs_eq (K : KitShape a) (r : Request) (k : rcKey a r) :
    (List.range (maskCount a r k)).flatMap (vecOf a K r k) = coordWordK K r k := by
  rw [MaskCoord.coordWordK_eq]
  exact flatMap_range_getD (PolyKit.vector (K.C r) (K.w r)) [] _

/-- **The loop's cells.** -/
def loopCells {K : KitShape a} (C : CellParts a K) (hA : ConeBounds.RouteA a K) (r : Request) (k : rcKey a r)
    (hk : k ∈ rcKeys a r) (R L Llog mb : ℕ)
    (hmb : ∀ j, j < maskCount a r k → C.mid.midCost r k j ≤ mb) (hmbR : mb ≤ R)
    (hlen : ∀ j, j < maskCount a r k → (vecOf a K r k j).length = L) (hLR : L ≤ R)
    (hR : CellParts.cellCost mb (C.app.cost L) (maskCount a r k) + 1 ≤ R) (hL : R + 1 ≤ Llog) :=
  Cells.ofScrub (n := CellParts.cellCost mb (C.app.cost L) (maskCount a r k)) C.cellMachine C.cellReset C.cellS
    R Llog (maskCount a r k) (fun _ out => C.cellHeads out) (fun j out => C.cellBank r k R L j out)
    (vecOf a K r k)
    (fun i hi => by
      simp only [CellParts.cellS, decide_eq_true_eq] at hi
      simp only [CellParts.cellReset, decide_eq_true_eq]
      omega)
    hR hL
    (fun _ _ out i hi => by
      simp only [CellParts.cellReset, decide_eq_true_eq] at hi
      simp only [CellParts.cellHeads, if_neg hi])
    (fun _ _ out i hi => by
      simp only [CellParts.cellS, decide_eq_true_eq] at hi
      exact cellBank_hi C r k R L _ out i hi)
    (fun j hj out => cell_stage C hA r k hk j hj out R L mb (hmb j hj) hmbR (hlen j hj) hLR)

section Proj

end Proj

/-- The loop as one `Step`, before the concatenated vectors are named (`Cells.loopStep` at `loopCells`; every
projection is definitional, so the statement is checked by `exact`, never by rewriting inside the machine). -/
theorem loop_run0 {K : KitShape a} (C : CellParts a K) (hA : ConeBounds.RouteA a K) (r : Request) (k : rcKey a r)
    (hk : k ∈ rcKeys a r) (R L Llog mb : ℕ)
    (hmb : ∀ j, j < maskCount a r k → C.mid.midCost r k j ≤ mb) (hmbR : mb ≤ R)
    (hlen : ∀ j, j < maskCount a r k → (vecOf a K r k j).length = L) (hLR : L ≤ R)
    (hR : CellParts.cellCost mb (C.app.cost L) (maskCount a r k) + 1 ≤ R) (hL : R + 1 ≤ Llog) :
    Step (CloseoutRowsDegreeLoop.machine (Scrub.machine C.cellMachine C.cellReset C.cellS))
      (maskCount a r k * (2 * CellParts.cellCost mb (C.app.cost L) (maskCount a r k) + 2 + 1 + (2 * R + 4) + 3) + 3)
      (Fin.addCases (Scrub.heads (C.cellHeads [])) (fun _ : Fin 1 => 1))
      (Fin.addCases (Scrub.bank (C.cellBank r k R L 0 []) R Llog)
        (fun _ : Fin 1 => CompareMachine.word (maskCount a r k)))
      (Fin.addCases (Scrub.heads (C.cellHeads ((List.range (maskCount a r k)).flatMap (vecOf a K r k))))
        (fun _ : Fin 1 => 1))
      (Fin.addCases (Scrub.bank (C.cellBank r k R L (maskCount a r k)
          ((List.range (maskCount a r k)).flatMap (vecOf a K r k))) R Llog)
        (fun _ : Fin 1 => CompareMachine.word (maskCount a r k))) :=
  Cells.loopStep (loopCells C hA r k hk R L Llog mb hmb hmbR hlen hLR hR hL) []

/-- The loop as one `Step` at any name `w` of the concatenated vectors. -/
theorem loop_runW {K : KitShape a} (C : CellParts a K) (hA : ConeBounds.RouteA a K) (r : Request) (k : rcKey a r)
    (hk : k ∈ rcKeys a r) (R L Llog mb : ℕ)
    (hmb : ∀ j, j < maskCount a r k → C.mid.midCost r k j ≤ mb) (hmbR : mb ≤ R)
    (hlen : ∀ j, j < maskCount a r k → (vecOf a K r k j).length = L) (hLR : L ≤ R)
    (hR : CellParts.cellCost mb (C.app.cost L) (maskCount a r k) + 1 ≤ R) (hL : R + 1 ≤ Llog)
    (w : List Bool) (hw : (List.range (maskCount a r k)).flatMap (vecOf a K r k) = w) :
    Step (CloseoutRowsDegreeLoop.machine (Scrub.machine C.cellMachine C.cellReset C.cellS))
      (maskCount a r k * (2 * CellParts.cellCost mb (C.app.cost L) (maskCount a r k) + 2 + 1 + (2 * R + 4) + 3) + 3)
      (Fin.addCases (Scrub.heads (C.cellHeads [])) (fun _ : Fin 1 => 1))
      (Fin.addCases (Scrub.bank (C.cellBank r k R L 0 []) R Llog)
        (fun _ : Fin 1 => CompareMachine.word (maskCount a r k)))
      (Fin.addCases (Scrub.heads (C.cellHeads w)) (fun _ : Fin 1 => 1))
      (Fin.addCases (Scrub.bank (C.cellBank r k R L (maskCount a r k) w) R Llog)
        (fun _ : Fin 1 => CompareMachine.word (maskCount a r k))) := by
  subst hw
  exact loop_run0 C hA r k hk R L Llog mb hmb hmbR hlen hLR hR hL

/-- **The whole mask loop as one `Step`**: from the empty output to the coordinate word (`vecs_eq`). -/
theorem loop_run {K : KitShape a} (C : CellParts a K) (hA : ConeBounds.RouteA a K) (r : Request) (k : rcKey a r)
    (hk : k ∈ rcKeys a r) (R L Llog mb : ℕ)
    (hmb : ∀ j, j < maskCount a r k → C.mid.midCost r k j ≤ mb) (hmbR : mb ≤ R)
    (hlen : ∀ j, j < maskCount a r k → (vecOf a K r k j).length = L) (hLR : L ≤ R)
    (hR : CellParts.cellCost mb (C.app.cost L) (maskCount a r k) + 1 ≤ R) (hL : R + 1 ≤ Llog) :
    Step (CloseoutRowsDegreeLoop.machine (Scrub.machine C.cellMachine C.cellReset C.cellS))
      (maskCount a r k * (2 * CellParts.cellCost mb (C.app.cost L) (maskCount a r k) + 2 + 1 + (2 * R + 4) + 3) + 3)
      (Fin.addCases (Scrub.heads (C.cellHeads [])) (fun _ : Fin 1 => 1))
      (Fin.addCases (Scrub.bank (C.cellBank r k R L 0 []) R Llog)
        (fun _ : Fin 1 => CompareMachine.word (maskCount a r k)))
      (Fin.addCases (Scrub.heads (C.cellHeads (coordWordK K r k))) (fun _ : Fin 1 => 1))
      (Fin.addCases (Scrub.bank (C.cellBank r k R L (maskCount a r k) (coordWordK K r k)) R Llog)
        (fun _ : Fin 1 => CompareMachine.word (maskCount a r k))) :=
  loop_runW C hA r k hk R L Llog mb hmb hmbR hlen hLR hR hL _ (vecs_eq K r k)

end
end NearCubicWires.PacketsConstruction.Residual

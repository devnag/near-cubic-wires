import Proof.Packets.PacketsCoordSwitch

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.Residual
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
noncomputable section

/-! ## `1^j ↦ 1^(j+1)` -/

namespace IncrM

/-- Walk right over the ones; write one more at the first blank. -/
def machine : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q b => if q.val = 0 then
      (if b 0 then some ⟨0, fun _ => none, fun _ => .right⟩ else some ⟨1, fun _ => some true, fun _ => .stay⟩)
    else none

def cfg (q : Fin 2) (p : ℕ) (tape : List Bool) : Configuration 1 2 := ⟨q, fun _ => p, fun _ => tape⟩

theorem move_step (j p : ℕ) (hp : p < j) :
    step machine (cfg 0 p (List.replicate j true)) = some (cfg 0 (p + 1) (List.replicate j true)) := by
  have hr : readTapeBit (List.replicate j true) p = true := by simp [readTapeBit, List.getD, hp]
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · funext i; simp [applyAction]

theorem write_step (j : ℕ) :
    step machine (cfg 0 j (List.replicate j true)) = some (cfg 1 j (List.replicate (j + 1) true)) := by
  have hr : readTapeBit (List.replicate j true) j = false := by simp [readTapeBit, List.getD]
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · funext i
    have h := Streaming.write_append (List.replicate j true) true
    rw [List.length_replicate] at h
    have hw : writeTapeBit (List.replicate j true) j true = List.replicate (j + 1) true :=
      h.trans (List.replicate_succ' (n := j) (a := true)).symm
    simp [applyAction, hw]

theorem walk (j : ℕ) : ∀ d p, p + d = j → Timed machine d (cfg 0 p (List.replicate j true)) (cfg 0 j (List.replicate j true))
  | 0, p, h => by
    rw [show p = j by omega]
    exact Timed.refl _ _
  | d + 1, p, h => Timed.step (by rfl) (move_step j p (by omega)) (walk j d (p + 1) (by omega))

theorem run (j : ℕ) :
    Step machine (j + 1) (fun _ => 0) (fun _ => List.replicate j true) (fun _ => j)
      (fun _ => List.replicate (j + 1) true) := by
  have ht := (walk j j 0 (by omega)).trans (Timed.single (by rfl) (write_step j))
  obtain ⟨r, hr, hf, _⟩ := ht.run (by rfl)
  exact Step.of_run (r := r) hr (by rw [hf]; rfl) (by rw [hf]; rfl)

end IncrM

/-! ## The cell -/

variable {a : DecompositionAlgorithm}

structure CellParts (a : DecompositionAlgorithm) (K : KitShape a) where
  mid : MidParts a K
  app : AppendStage

namespace CellParts
variable {K : KitShape a} (C : CellParts a K)

/-- The cell bank's size. -/
def Tc : ℕ := C.mid.Tm + 3 + C.app.extra

theorem Tc_ge : 755 ≤ C.Tc := by have := C.mid.Tm_ge; unfold Tc; omega

/-- The middle's tapes: `0..9` in place, the rest shifted by two (the log `Tm ↦ Tm + 2`). -/
def σM (i : Fin (C.mid.Tm + 1)) : Fin C.Tc :=
  ⟨if i.val < 10 then i.val else i.val + 2, by have := i.isLt; unfold Tc; split_ifs <;> omega⟩

/-- The append's tapes: source 716, output 11, driver 10, private tapes after the middle. -/
def σA (l : Fin (3 + C.app.extra)) : Fin C.Tc :=
  ⟨if l.val = 0 then 716 else if l.val = 1 then 11 else if l.val = 2 then 10 else C.mid.Tm + 3 + (l.val - 3), by
    have := l.isLt; have := C.mid.Tm_ge; unfold Tc; split_ifs <;> omega⟩

/-- The increment's tape: the mask index. -/
def σI (_ : Fin 1) : Fin C.Tc := ⟨9, by have := C.Tc_ge; omega⟩

theorem σM_val (i : Fin (C.mid.Tm + 1)) : (C.σM i).val = if i.val < 10 then i.val else i.val + 2 := rfl
theorem σA_val (l : Fin (3 + C.app.extra)) : (C.σA l).val =
    if l.val = 0 then 716 else if l.val = 1 then 11 else if l.val = 2 then 10 else C.mid.Tm + 3 + (l.val - 3) := rfl

theorem σM_injective : Function.Injective C.σM := by
  intro x y h
  have hv := congrArg Fin.val h
  rw [σM_val, σM_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem σA_injective : Function.Injective C.σA := by
  intro x y h
  have hv := congrArg Fin.val h
  rw [σA_val, σA_val] at hv
  have := C.mid.Tm_ge
  apply Fin.ext
  split_ifs at hv <;> omega

theorem σI_injective : Function.Injective C.σI := by
  intro x y _
  exact Subsingleton.elim x y

/-- **The cell machine.** -/
def cellMachine :=
  Composition.machine (Composition.machine
    (RecoveryFocus.machine C.σM (MaskedReset.machine C.mid.midMachine (fun _ => true)))
    (RecoveryFocus.machine C.σA C.app.machine)) (RecoveryFocus.machine C.σI IncrM.machine)

/-- The `j`-th cell bank. -/
def cellBank (r : Request) (k : rcKey a r) (R L j : ℕ) (out : List Bool) (i : Fin C.Tc) : List Bool :=
  if i.val < 9 then PacketsCombine.metaEntry a r (some k) C.Tc i
  else if i.val = 9 then List.replicate j true
  else if i.val = 10 then List.replicate L true
  else if i.val = 11 then out else List.replicate R false

def cellHeads (out : List Bool) (i : Fin C.Tc) : ℕ := if i.val = 11 then out.length else 0

/-- Scratch: tapes 12 and up. Reset: every tape but the output. -/
def cellS (i : Fin C.Tc) : Bool := decide (12 ≤ i.val)
def cellReset (i : Fin C.Tc) : Bool := decide (i.val ≠ 11)

def cellCost (mb aL M : ℕ) : ℕ := 2 * mb + 2 + 1 + aL + 1 + (M + 1)

end CellParts

/-- Mask `j`'s vector. -/
def vecOf (a : DecompositionAlgorithm) (K : KitShape a) (r : Request) (k : rcKey a r) (j : ℕ) : List Bool :=
  PolyKit.vector (K.C r) (K.w r) ((MaskCoord.maskCoordsList a r k).getD j [])

end
end NearCubicWires.PacketsConstruction.Residual

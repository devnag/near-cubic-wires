import Proof.Packets.PacketFamilyParent
import Proof.MachineModel.BlockScrub

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketFamilyParent
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.BlockPlatform
open NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

/-- Residents of the scrubbed layout: the shared log, then the driver. -/
def scrubResidentA (R : ℕ) : Fin 2 → List Bool :=
  fun i => if i.val = 0 then List.replicate (R+1) false else List.replicate R true

theorem flat_inner {α : Type} {t : ℕ} (H : Fin t → α) (f : Fin 2 → α) (i : Fin t) :
    Fin.addCases (m := t) (n := 2) (motive := fun _ => α) H f (Fin.castAdd 1 (Fin.castAdd 1 i)) = H i := by
  have he : (Fin.castAdd 1 (Fin.castAdd 1 i) : Fin (t + 1 + 1)) = Fin.castAdd 2 i := Fin.ext rfl
  rw [he]
  exact Fin.addCases_left i

theorem flat_log {α : Type} {t : ℕ} (H : Fin t → α) (f : Fin 2 → α) :
    Fin.addCases (m := t) (n := 2) (motive := fun _ => α) H f (Fin.castAdd 1 (Fin.natAdd t (0 : Fin 1))) = f 0 := by
  have he : (Fin.castAdd 1 (Fin.natAdd t (0 : Fin 1)) : Fin (t + 1 + 1)) = Fin.natAdd t (0 : Fin 2) :=
    Fin.ext rfl
  rw [he]
  exact Fin.addCases_right (0 : Fin 2)

theorem flat_driver {α : Type} {t : ℕ} (H : Fin t → α) (f : Fin 2 → α) :
    Fin.addCases (m := t) (n := 2) (motive := fun _ => α) H f (Fin.natAdd (t + 1) (0 : Fin 1)) = f 1 := by
  have he : (Fin.natAdd (t + 1) (0 : Fin 1) : Fin (t + 1 + 1)) = Fin.natAdd t (1 : Fin 2) :=
    Fin.ext (by simp)
  rw [he]
  exact Fin.addCases_right (1 : Fin 2)

theorem scrub_heads_flat {t : ℕ} (H : Fin t → ℕ) :
    Scrub.heads H = (Fin.addCases H (fun _ : Fin 2 => 0) : Fin (t + 2) → ℕ) := by
  funext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · refine Fin.addCases (fun i => ?_) (fun k => ?_) k
    · change Scrub.heads H (Scrub.inner i) = _
      rw [Scrub.heads_inner]
      exact (flat_inner H (fun _ => 0) i).symm
    · rw [Fin.eq_zero k]
      change Scrub.heads H Scrub.logTape = _
      rw [Scrub.heads_log]
      exact (flat_log H (fun _ => 0)).symm
  · rw [Fin.eq_zero k]
    change Scrub.heads H Scrub.driverTape = _
    rw [Scrub.heads_driver]
    exact (flat_driver H (fun _ => 0)).symm

theorem scrub_bank_flat {t : ℕ} (A : Fin t → List Bool) (R : ℕ) :
    Scrub.bank A R (R+1) = (Fin.addCases A (scrubResidentA R) : Fin (t + 2) → List Bool) := by
  funext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · refine Fin.addCases (fun i => ?_) (fun k => ?_) k
    · change Scrub.bank A R (R+1) (Scrub.inner i) = _
      rw [Scrub.bank_inner]
      exact (flat_inner A (scrubResidentA R) i).symm
    · rw [Fin.eq_zero k]
      change Scrub.bank A R (R+1) Scrub.logTape = _
      rw [Scrub.bank_log]
      exact (flat_log A (scrubResidentA R)).symm
  · rw [Fin.eq_zero k]
    change Scrub.bank A R (R+1) Scrub.driverTape = _
    rw [Scrub.bank_driver]
    exact (flat_driver A (scrubResidentA R)).symm

/-- **The cleanup field, from `Scrub.step`** (reset set = scratch set). -/
def blockScrubForm (t : ℕ) (S : Fin t → Bool) : ScrubForm t S where
  extra := 2
  states := fun s => s + 2 + 4
  wrap := fun M => Scrub.machine M S S
  residentH := fun _ _ => 0
  residentA := scrubResidentA
  cost := fun n R => 2*n+2+1+(2*R+4)
  factor := 7
  cost_le := by intro n R; omega
  run := by
    intro s M n R H H' A A' h hR hS
    have hs := Scrub.step h S S R (R+1) (fun i hi => (hS i hi).1) (fun _ hi => hi)
      (fun i hi => (hS i hi).2) hR (le_refl _)
    rw [scrub_heads_flat, scrub_bank_flat, scrub_heads_flat, scrub_bank_flat] at hs
    exact hs

/-! ## The residual with every supplied field plugged in

Keys are the checked closeout keys (`rcFiveKeys`), cleanup is `blockScrubForm`.
What is left is exactly: the layout decision, the P1 writer, the cursor, the
setup (drivers: `word rows` and `replicate R true`; cursor start; residents), and
`writer.cost + 1 ≤ R`. -/
structure SuppliedResidual (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) where
  layout : Layout a (rcFiveKeys a)
  writer : RowWriter selector layout
  cursor : CursorAdvance layout
  setup : Setup layout (blockScrubForm layout.tapes layout.scratch)
  widthFits : ∀ r, writer.cost r + 1 ≤ layout.width r

def SuppliedResidual.toContract {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    (x : SuppliedResidual selector a) : RowWriterContract selector a where
  keys := rcFiveKeys a
  layout := x.layout
  writer := x.writer
  cursor := x.cursor
  scrub := blockScrubForm x.layout.tapes x.layout.scratch
  setup := x.setup
  widthFits := x.widthFits

theorem packetConstruction_of_residual (selector : CyclicChoice.Laws)
    (h : ∀ a, Nonempty (SuppliedResidual selector a)) : PacketConstruction selector :=
  packetConstruction_of_contract selector (fun a => (h a).elim fun x => ⟨x.toContract⟩)

end
end NearCubicWires.PacketFamilyParent

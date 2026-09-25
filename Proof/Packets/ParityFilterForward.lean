import Proof.Packets.ParityFilterBody

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ParityFilter
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization

 theorem boot_forward (i : Fin 9) : CursorRestore.NoLeft boot i := by
  intro q bits a ha
  fin_cases q <;> simp [boot] at ha
  subst a
  simp

theorem embed_extra_forward {t e s : Nat} (p : Machine t s) (i : Fin e) :
    CursorRestore.NoLeft (TapeEmbedding.machine e p) (i.natAdd t) := by
  intro q bits a ha
  cases hr : p.rule q (fun j=>bits (j.castAdd e)) with
  | none => simp [TapeEmbedding.machine,hr] at ha
  | some b =>
    simp [TapeEmbedding.machine,hr] at ha
    subst a
    simp [TapeEmbedding.action]

theorem select_forward (i : Fin 4) : CursorRestore.NoLeft MaskSelect.machine i := by
  intro q bits a ha
  fin_cases q <;> simp [MaskSelect.machine] at ha
  all_goals subst a
  all_goals fin_cases i <;> simp
  all_goals split <;> simp

theorem output_forward : CursorRestore.NoLeft body 7 :=
  CursorRestore.composition_forward boot tail 7 (boot_forward 7)
    (CursorRestore.composition_forward scan emit 7
      (embed_extra_forward PhysicalParityRestore.machine (0 : Fin 2))
      (CursorRestore.focus_forward slots slots_injective MaskSelect.machine 1 (select_forward 1)))

theorem count_forward : CursorRestore.NoLeft body 8 :=
  CursorRestore.composition_forward boot tail 8 (boot_forward 8)
    (CursorRestore.composition_forward scan emit 8
      (embed_extra_forward PhysicalParityRestore.machine (1 : Fin 2))
      (CursorRestore.focus_forward slots slots_injective MaskSelect.machine 2 (select_forward 2)))

end PCJ9eff70d512234a4c_Fixed.Materializer.ParityFilter

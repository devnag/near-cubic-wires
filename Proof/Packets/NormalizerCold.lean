import Proof.Packets.NormalizerMaterialize
import Proof.Packets.NormalizerData

/-! Complete cold-entry normalization. Scratch is truly blank initially;
the zero reserves used in internal proofs are removed by the interpreter's
proved padding transport, and flag/count sentinels are written by boot. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizeCold
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding

noncomputable def machine := Composition.machine boot Normalize.machine
noncomputable def entry (B : Nat) (raw : List (List Bool)) := Normalize.started machine heads (data B raw)
def budget (B : Nat) (raw : List (List Bool)) := Normalize.budget B raw+2

theorem seeded_run (B : Nat) (raw : List (List Bool)) (hw : ∀ bits∈raw,bits.length=B) :
    ∃ r,runFrom Normalize.machine (Normalize.budget B raw) (seededEntry B raw)=some r ∧
      r.steps≤Normalize.budget B raw ∧
      r.final.tapes 20=(NormalizerOrder.ordered raw).flatten ∧ r.final.heads 20=0 ∧
      r.final.tapes 21=CompareMachine.word (NormalizerOrder.ordered raw).length ∧ r.final.heads 21=1 := by
  obtain ⟨a,ha,has,aout,ahout,acount,ahcount⟩ := Normalize.run B raw hw
  rw [←padded_entry] at ha
  obtain ⟨r,hr,hrf,hrs,_⟩ := ZeroPadding.run_unpad Normalize.machine (capacities B raw.length) _ _ a ha
  refine ⟨r,hr,hrs.le.trans has,?_,?_,?_,?_⟩
  · have h := congrArg (fun c=>c.tapes 20) hrf
    simpa [ZeroPadding.config,capacities,aout] using h
  · have h := congrArg (fun c=>c.heads 20) hrf
    simpa [ZeroPadding.config,ahout] using h
  · have h := congrArg (fun c=>c.tapes 21) hrf
    simpa [ZeroPadding.config,capacities,acount] using h
  · have h := congrArg (fun c=>c.heads 21) hrf
    simpa [ZeroPadding.config,ahcount] using h

/-- The fixed machine produces the complete literal ordered parity-normal
mask bank and a runtime unary count from the resident raw support records.
Entry scratch is empty; no coefficient/candidate/normalized bytes are inputs. -/
theorem run (B : Nat) (raw : List (List Bool)) (hw : ∀ bits∈raw,bits.length=B) :
    ∃ r,runFrom machine (budget B raw) (entry B raw)=some r ∧ r.steps≤budget B raw ∧
      r.final.tapes 20=(NormalizerOrder.ordered raw).flatten ∧ r.final.heads 20=0 ∧
      r.final.tapes 21=CompareMachine.word (NormalizerOrder.ordered raw).length ∧ r.final.heads 21=1 := by
  obtain ⟨a,ha,haf,has⟩ := boot_run B raw
  obtain ⟨b,hb,hbs,bout,bhout,bcount,bhcount⟩ := seeded_run B raw hw
  have hj : runFrom Normalize.machine (Normalize.budget B raw)
      (Composition.restart a.final Normalize.machine.start)=some b := by
    rw [haf]
    exact hb
  have h := Composition.run_join boot Normalize.machine _ _ _ a b ha hj
  have ht : 1+1+Normalize.budget B raw=budget B raw := by unfold budget; omega
  rw [ht] at h
  refine ⟨_,h,?_,bout,bhout,bcount,bhcount⟩
  change a.steps+1+b.steps≤budget B raw
  rw [has]
  unfold budget
  omega

end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizeCold

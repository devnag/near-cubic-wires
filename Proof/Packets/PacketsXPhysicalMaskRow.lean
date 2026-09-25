import Proof.Packets.PacketsXPhysicalMaskIndices
import Proof.Packets.PhysicalMaskReset
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.PhysicalMaskRow
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch PhysicalMaskIndices

def capacity (B : Nat) : Fin 4 → Nat := ![0,0,B+3,0]
def machine := Composition.machine PhysicalMaskSerialize.machine PhysicalMaskReset.machine
def input (bankPre support suffix out : List Bool) :=
  Composition.leftConfig 4 (ZeroPadding.config (capacity support.length)
    (PhysicalMaskSerialize.Bank.ready bankPre support suffix 0 0 out))
def ending (B : Nat) (source : List Bool) (sourcePos : Nat) (out : List Bool) :=
  Composition.rightConfig 7
    (PhysicalMaskReset.cfg B source sourcePos 3 1
      (ZeroPadding.pad (B+3) (UnaryTemplate.tape 1)) 1 out)

theorem boundary (bankPre support suffix out : List Bool) :
    Composition.restart
      (ZeroPadding.config (capacity support.length)
        (PhysicalMaskSerialize.Bank.ready bankPre support suffix 6 support.length out))
      PhysicalMaskReset.machine.start =
    PhysicalMaskReset.cfg support.length (bankPre++support++suffix) (bankPre.length+support.length)
      0 (support.length+1) (UnaryTemplate.tape (support.length+1)) 1 out := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i; fin_cases i <;>
      simp [Composition.restart,ZeroPadding.config,capacity,PhysicalMaskSerialize.Bank.ready,
        PhysicalMaskSerialize.Bank.cfg,PhysicalMaskReset.cfg,ZeroPadding.pad]

theorem row_run (bankPre support suffix out : List Bool) :
    ∃ r, runFrom machine (support.length^2+8*support.length+6)
      (input bankPre support suffix out)=some r ∧
      r.final=ending support.length (bankPre++support++suffix) (bankPre.length+support.length)
        (out++ExtIncidence.monomialWord (selectedIndices 0 support)) ∧
      r.steps=support.length^2+8*support.length+6 := by
  obtain ⟨a,ha,haf,has⟩ := PhysicalMaskSerialize.Bank.padded_run bankPre support suffix out
    (capacity support.length)
  obtain ⟨b,hb,hbf,hbs⟩ := PhysicalMaskReset.reset_run support.length
    (bankPre++support++suffix) (bankPre.length+support.length)
    (out++ExtIncidence.monomialWord (selectedIndices 0 support))
  have join : runFrom PhysicalMaskReset.machine (2*support.length+3)
      (Composition.restart a.final PhysicalMaskReset.machine.start)=some b := by
    rw [haf,boundary]
    exact hb
  have h := Composition.run_join PhysicalMaskSerialize.machine PhysicalMaskReset.machine _ _ _ a b ha join
  have ht : support.length^2+6*support.length+2+1+(2*support.length+3)=support.length^2+8*support.length+6 := by ring
  rw [ht] at h
  refine ⟨Composition.joinedReceipt a b,h,?_,?_⟩
  · simp only [Composition.joinedReceipt,ending,hbf]
  · simp only [Composition.joinedReceipt,has,hbs]
    exact ht

end PCJ9eff70d512234a4c_Fixed.PhysicalMaskRow

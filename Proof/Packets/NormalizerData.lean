import Proof.Packets.NormalizerMaterializeData

/-! Fresh scratch input and the one executed initializer for normalization.
Only the source records, their actual count, and the width template are present. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizeCold
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding
open Normalize

def heads : Fin 24→Nat := fun i=>if i=3 ∨ i=13 then 1 else 0
def data (B : Nat) (raw : List (List Bool)) : Fin 24→List Bool := fun i=>
  if i=0 then SuffixScan.stream (records raw)
  else if i=3 then CompareMachine.word raw.length
  else if i=13 then UnaryTemplate.tape (2*B+3) else []
def seededHeads : Fin 24→Nat := fun i=>if i=3 ∨ i=13 ∨ i=21 then 1 else 0
def seededData (B : Nat) (raw : List (List Bool)) : Fin 24→List Bool := fun i=>
  if i=16 ∨ i=17 ∨ i=21 then [false] else data B raw i

def boot : Machine 24 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then
    some ⟨1,fun i=>if i=16 ∨ i=17 ∨ i=21 then some false else none,
      fun i=>if i=21 then .right else .stay⟩ else none

def bootCfg (q : Fin 2) (B : Nat) (raw : List (List Bool)) :=
  (⟨q,heads,data B raw⟩ : Configuration 24 2)
def bootFinal (B : Nat) (raw : List (List Bool)) :=
  (⟨1,seededHeads,seededData B raw⟩ : Configuration 24 2)
noncomputable def seededEntry (B : Nat) (raw : List (List Bool)) :=
  Normalize.started Normalize.machine seededHeads (seededData B raw)

def capacities (B M : Nat) : Fin 24→Nat := fun i=>
  if i=15 then reverseCap B M else if i=18 then probeCap B else if i=19 then scanCap B M
  else if i=22 then filterCap B M else if i=23 then countCap B M else 0

theorem boot_step (B : Nat) (raw : List (List Bool)) :
    step boot (bootCfg 0 B raw)=some (bootFinal B raw) := by
  simp only [step,boot,bootCfg]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,heads,seededHeads,bootFinal]
  · funext i; fin_cases i <;> simp [applyAction,seededData,data,bootFinal,writeTapeBit,heads]

theorem boot_run (B : Nat) (raw : List (List Bool)) :
    ∃ r,runFrom boot 1 (bootCfg 0 B raw)=some r ∧ r.final=bootFinal B raw ∧ r.steps=1 :=
  (Timed.single (by rfl) (boot_step B raw)).run (by rfl)

theorem padded_entry (B : Nat) (raw : List (List Bool)) :
    ZeroPadding.config (capacities B raw.length) (seededEntry B raw)=Normalize.entry B raw := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;>
      simp [ZeroPadding.config,seededEntry,seededHeads,Normalize.entry,Normalize.started,
        Normalize.dedupEntry,extraHeads,TapeEmbedding.config,Fin.addCases,DedupMaterialReady.entry,
        Composition.leftConfig,Rewind.recording,Rewind.config,DedupCold.entry]
  · funext i; fin_cases i <;>
      simp [ZeroPadding.config,ZeroPadding.pad,capacities,seededEntry,seededData,data,Normalize.entry,Normalize.started,
        Normalize.dedupEntry,extraData,TapeEmbedding.config,Fin.addCases,DedupMaterialReady.entry,
        Composition.leftConfig,Rewind.recording,Rewind.config,DedupCold.entry,CompareMachine.word]

end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizeCold

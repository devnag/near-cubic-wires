import Proof.Packets.PacketsXWindowModeCacheLayout
import Proof.Packets.PacketsXWindowLevelAtomLayout

/-! One fixed level-cache producer: emit both original-seed mode-cache halves,
then construct the reflected literal cache and its dense normalized atoms.
The execution of each constituent is discharged by its concrete run theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 10000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeCache
open CloseoutRowsRawPairSeek (Pair)
open Theorem25Completion.CycleBounds Theorem25Completion.CycleDenseAtomCost
noncomputable section

attribute [local irreducible] buildModeCache levelAtoms

def modePairs (p : Parameters) (M : Nat) := pairs 1 p M++pairs 2 p M
def modeAtoms := Composition.machine buildModeCache levelAtoms
def modeAtomsBudget (p : Parameters) (M C R : Nat) :=
  ModeCacheReady.budget p M R+1+levelAtomsBudget C R (p.level+1) (modePairs p M).length
def modeAtomsOutput (p : Parameters) (M C R : Nat)
    (initial : List PacketVector.Packet) (A : Fin 256 → List Bool) :=
  levelAtomsOutput C R (p.level+1) (modePairs p M) initial (modeOutput p M R A)

theorem mode_output_late (p : Parameters) (M R : Nat) (A : Fin 256 → List Bool)
    (i : Fin 256) (hi : 176 ≤ i.val) : modeOutput p M R A i=A i := by
  apply mode_output_outside
  intro j he
  have hsmall : ∀j,(modePorts j).val<176 := by decide
  have h:=hsmall j
  rw [he] at h
  omega

theorem mode_output_work (p : Parameters) (M R : Nat) (A : Fin 256 → List Bool)
    (i : Fin 256) (hi : Workspace.selected i) : modeOutput p M R A i=A i := by
  apply mode_output_outside
  intro j he
  have away : ∀j,¬Workspace.selected (modePorts j) := by decide
  exact away j (he.symm ▸ hi)

theorem mode_atoms_run (p : Parameters) (M C w : Nat)
    (out : List Bool) (priv : Fin 15 → List Bool) (initial : List PacketVector.Packet)
    (hl : p.level ≤ p.rank) (hC : p.rank+2 ≤ p.C)
    (hb : CloseoutRowsModeHashLoop.budget p.rank p.rank+2 ≤ p.C)
    (hi : M ≤ 2^p.rank) (hlog : sourceBudget p M ≤ commonReserve C w+3)
    (hD : reuseCapacity p M ≤ commonReserve C w)
    (hpriv : ∀i,(priv i).length ≤ commonReserve C w)
    (hout : out.length ≤ commonReserve C w)
    (hword : (ModeCacheReady.word p M).length ≤ commonReserve C w)
    (hw : 1 ≤ w) (htag : p.level+1 ≤ C) (hcount : (modePairs p M).length ≤ C)
    (hcodes : ∀i<(modePairs p M).length,Nat.pair (p.level+1) i<C)
    (hshape : ∀pair∈modePairs p M,AtomShape C pair)
    (hinit : initial.length=C) (hinits : ∀P∈initial,PacketVector.Fits (commonReserve C w) P)
    (left : PacketVector.Packet) (A : Fin 256 → List Bool)
    (hengine : ∀i : Fin 34,A (i.castAdd 222)=ReusableArithmetic.state C (commonReserve C w) left [] i)
    (hmode : ∀i,ModeCacheReady.A p M (commonReserve C w) out priv i=A (modePorts i))
    (atag : A 187=ZeroPadding.pad (commonReserve C w) (CompareMachine.word (p.level+1)))
    (acount : A 184=ZeroPadding.pad (commonReserve C w) (CompareMachine.word (modePairs p M).length))
    (abank : A 140=PacketVector.bank (commonReserve C w) initial)
    (hprivate : ∀i,i≠59 → i≠60 → i≠62 → i≠64 → i≠65 → (A (literalPorts i)).length ≤ commonReserve C w)
    (hwork : ∀i,Workspace.selected i → (A i).length ≤ commonReserve C w)
    (h129 : (A 129).length ≤ commonReserve C w) :
    Step modeAtoms (modeAtomsBudget p M C (commonReserve C w)) heads A heads
      (modeAtomsOutput p M C (commonReserve C w) initial A) := by
  let R:=commonReserve C w
  let B:=modeOutput p M R A
  have first:=build_mode_cache_run p M R out priv hl hC hb hi hlog hD hpriv hout hword
    heads A (by decide) hmode
  have bankB : B 140=PacketVector.bank R initial := by
    dsimp only [B]
    rw [mode_output_outside p M R A 140 (by decide)]
    exact abank
  have privateB : ∀i,i≠59 → i≠60 → i≠62 → i≠64 → i≠65 → (B (literalPorts i)).length ≤ R := by
    intro i h59 h60 h62 h64 h65
    have late : ∀i : Fin 68,i≠59 → i≠60 → i≠62 → i≠64 → i≠65 → 176 ≤ (literalPorts i).val := by decide
    dsimp only [B]
    rw [mode_output_late p M R A _ (late i h59 h60 h62 h64 h65)]
    exact hprivate i h59 h60 h62 h64 h65
  have last:=level_atoms_run C w (p.level+1) (modePairs p M) initial hw htag hcount hcodes hshape hinit hinits
    left B (mode_output_engine p M C R left [] A hengine)
    ((mode_output_late p M R A 187 (by decide)).trans atag)
    ((mode_output_late p M R A 184 (by decide)).trans acount)
    (mode_source p M R A) bankB privateB
    (by intro i hi;dsimp only [B];rw [mode_output_work p M R A i hi];exact hwork i hi)
    (by dsimp only [B];rw [mode_output_outside p M R A 129 (by decide)];exact h129)
  exact first.seq last

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider

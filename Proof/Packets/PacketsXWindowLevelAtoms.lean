import Proof.Packets.PacketsXWindowDensePrepare
import Proof.Packets.PacketsXWindowLiteralCacheLayout

/-! Closed level preparation after the actual native mode cache is produced:
build the reflected literal codes, initialize physical dense-loop inputs,
and materialize their normalized atoms in the resident dense table. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsRawPairSeek (Pair cacheWord)
open Theorem25Completion.CycleBounds Theorem25Completion.CycleDenseAtomCost

def heads (i : Fin 256) : Nat := if i=31 then 1 else 0
theorem literal_heads : ∀i,LiteralCacheTransaction.heads i=heads (literalPorts i) := by decide
theorem workspace_heads : ∀j,heads (Workspace.slots j)=0 := by decide
theorem dense_heads : ∀i,DenseAtomBoundary.heads i=heads (densePorts i) := by decide

attribute [local irreducible] buildLiteralCache prepareDense buildDense
noncomputable def levelAtoms := Composition.machine buildLiteralCache
  (Composition.machine prepareDense buildDense)
def levelAtomsBudget (C R tag count : Nat) :=
  LiteralCacheTransaction.budget R tag count+1+((6*R+12)+1+DenseAtomBoundary.budget C R count)
noncomputable def levelAtomsOutput (C R tag : Nat) (cs : List Pair) (initial : List PacketVector.Packet) (A : Fin 256→List Bool) :=
  Function.update (denseReady R (cacheOutput R tag cs.length A)) 140
    (PacketVector.bank R (DenseAtomProgram.table C tag cs initial cs.length))
attribute [local irreducible] levelAtoms

theorem level_atoms_run (C w tag : Nat) (cs : List Pair) (initial : List PacketVector.Packet)
    (hw : 1≤w) (htag : tag≤C) (hcount : cs.length≤C) (hcodes : ∀i<cs.length,Nat.pair tag i<C)
    (hshape : ∀p∈cs,AtomShape C p)
    (hinit : initial.length=C) (hinits : ∀P∈initial,PacketVector.Fits (commonReserve C w) P)
    (left : PacketVector.Packet) (A : Fin 256→List Bool)
    (hengine : ∀i : Fin 34,A (i.castAdd 222)=ReusableArithmetic.state C (commonReserve C w) left [] i)
    (atag : A 187=ZeroPadding.pad (commonReserve C w) (CompareMachine.word tag))
    (acount : A 184=ZeroPadding.pad (commonReserve C w) (CompareMachine.word cs.length))
    (acache : A 125=ZeroPadding.pad (commonReserve C w) (cacheWord cs))
    (abank : A 140=PacketVector.bank (commonReserve C w) initial)
    (hprivate : ∀i,i≠59→i≠60→i≠62→i≠64→i≠65→(A (literalPorts i)).length≤commonReserve C w)
    (hwork : ∀i,Workspace.selected i→(A i).length≤commonReserve C w)
    (h129 : (A 129).length≤commonReserve C w) :
    Step levelAtoms (levelAtomsBudget C (commonReserve C w) tag cs.length) heads A heads
      (levelAtomsOutput C (commonReserve C w) tag cs initial A) := by
  let R:=commonReserve C w
  have hcap : C+2≤R := LiteralCacheReuse.reserve_width C w
  have a32 : A 32=List.replicate R true := hengine 32
  have a33 : A 33=List.replicate (R+3) false := hengine 33
  have a31 : A 31=UnaryTemplate.tape R := hengine 31
  have retained := cache_retained R tag cs.length A a32 a33 a31 atag acount (by omega) (by omega)
  let B:=cacheOutput R tag cs.length A
  have engine : ∀i : Fin 34,B (i.castAdd 222)=ReusableArithmetic.state C R left [] i := by
    intro i
    have hi:=i.isLt
    have hn : i.castAdd 222≠(186 : Fin 256) := by intro he;have he' : i.val=186 := congrArg (fun k : Fin 256=>k.val) he;omega
    exact (retained _ (by simp only [Fin.val_castAdd];omega) hn).trans (hengine i)
  have first:=build_literal_cache_run C w tag cs.length htag hcount (fun i hi=>(hcodes i hi).le)
    heads A literal_heads a32 a33 a31 atag acount hprivate
  have reserveEq : Theorem25Completion.CycleLiteralPairCost.commonReserve C w=commonReserve C w := rfl
  rw [reserveEq] at first
  have countB : B 184=ZeroPadding.pad R (CompareMachine.word cs.length) :=
    (retained 184 (by decide) (by decide)).trans acount
  have workB : ∀i,Workspace.selected i→(B i).length≤R := by
    intro i hi
    have hi' : i.val<188 ∧ i≠186 := by
      unfold Workspace.selected at hi
      constructor
      · omega
      · intro he;subst i;norm_num at hi
    dsimp only [B]
    rw [retained i hi'.1 hi'.2]
    exact hwork i hi
  have ready:=prepare_dense_run R heads B workspace_heads rfl rfl rfl
    (engine 32) (engine 33) (engine 31)
    (by rw [countB,ZeroPadding.pad_length,CompareMachine.word];simp only [List.length_cons,List.length_replicate,List.length_nil];omega)
    workB (by dsimp only [B];rw [retained 129 (by decide) (by decide)];exact h129)
  have input:=dense_ready_layout C R tag cs initial left B (by omega) engine
    ((retained 125 (by decide) (by decide)).trans acache)
    (by rw [DenseAtomMaterialize.codes_reflected];exact produced_cache R tag cs.length A)
    countB ((retained 140 (by decide) (by decide)).trans abank)
  have last:=build_dense_run C w tag cs initial hw hcount hcodes hshape hinit hinits
    heads (denseReady R B) dense_heads input
  simpa only [levelAtoms,levelAtomsBudget,levelAtomsOutput,R,B] using first.seq (ready.seq last)

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider

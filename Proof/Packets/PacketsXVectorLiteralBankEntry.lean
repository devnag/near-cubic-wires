import Proof.Packets.PacketsXVectorDenseInitialize
import Proof.Packets.PacketsXVectorLiteralInitialization

/-! All three banks are empty at entry to this initialization program. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeCache
noncomputable section

theorem bank_provider_other (C R : Nat) (left right : PacketVector.Packet)
    (fields : Fin 222 → List Bool) (bank : List Bool) (i : Fin 256) (hi : i≠140) :
    providerA C R left right (Function.update fields 106 bank) i=providerA C R left right fields i := by
  revert hi
  refine Fin.addCases (m:=34) (n:=222) (fun j=>?_) (fun j=>?_) i
  · intros;simp only [providerA,Fin.addCases_left]
  · intro hi
    have hj : j≠106 := by intro he;subst j;exact hi rfl
    simp only [providerA,Fin.addCases_right,Function.update_of_ne hj]

theorem cold_state_bank (C R M root depth : Nat) (p : Parameters)
    (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool) (oldBank newBank : List Bool)
    (h : LiteralColdState C R M root depth p fields extra oldBank) :
    LiteralColdState C R M root depth p (Function.update fields 106 newBank) extra newBank := by
  have ready : ProviderReady C R (Function.update fields 106 newBank) := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro left right i hi
      have hn : i≠140 := by unfold WindowProvider.Workspace.selected at hi;intro he;subst i;norm_num at hi
      rw [bank_provider_other C R left right fields newBank i hn]
      exact h.ready.work left right i hi
    · intro left right j
      have hn : ∀j,WindowProvider.seedPorts (WindowSeed.privateSlot j)≠140 := by decide
      rw [bank_provider_other C R left right fields newBank _ (hn j)]
      exact h.ready.seedWords left right j
    · simpa [Function.update] using h.ready.frame180
    · simpa [Function.update] using h.ready.frame181
    · simpa [Function.update] using h.ready.frame182
  refine ⟨ready,h.cold,h.logWord,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [Function.update] using h.rootWord
  · simpa [Function.update] using h.windowWord
  · simpa [Function.update] using h.tagLength
  · obtain ⟨out,priv,ho,hp,hm⟩:=h.modeWords
    refine ⟨out,priv,ho,hp,?_⟩
    intro left right i hi hj
    have hn : ∀i,WindowProvider.modePorts i≠140 := by decide
    rw [bank_provider_other C R left right fields newBank _ (hn i)]
    exact hm left right i hi hj
  · simpa [Function.update] using h.width
  · simpa [Function.update] using h.sourcePopulation
  · simpa [Function.update] using h.sourceDepth
  · simpa [Function.update] using h.blankMode
  · simpa [Function.update] using h.blankDigit
  · simp
  · intro left right i h59 h60 h62 h64 h65
    have hn : ∀i,WindowProvider.literalPorts i≠140 := by decide
    rw [bank_provider_other C R left right fields newBank _ (hn i)]
    exact h.privateLength left right i h59 h60 h62 h64 h65
  · simpa [Function.update] using h.denseCountLength
  · simpa [Function.update] using h.levelLength
  · simpa [Function.update] using h.tempLength

theorem cold_data_update_bank (C R : Nat) (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool)
    (bank : List Bool) :
    Function.update (coldData C R fields extra) 140 bank=coldData C R (Function.update fields 106 bank) extra := by
  unfold coldData
  change Function.update (Fin.addCases (m:=298) (n:=1) (motive:=fun _=>List Bool) _ _)
    (((140 : Fin 296).castAdd 2).castAdd 1) bank=_
  rw [PhysicalAppendUpdate.left,PhysicalAppendUpdate.left]
  rw [show (140 : Fin 296)=((106 : Fin 222).natAdd 34).castAdd 40 from rfl,update_meta]

def initializeLiteral := Composition.machine VectorNumericArena.initializeDense VectorNumericArena.initializeController
def initializeLiteralFuel (C R M : Nat) := VectorNumericArena.denseBudget R C+1+VectorNumericArena.initializeBudget R C M
attribute [local irreducible] VectorNumericArena.initializeController VectorNumericArena.initializeDense

theorem initialize_literal_run (C R M root depth : Nat) (p : Parameters)
    (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool)
    (h : LiteralColdState C R M root depth p fields extra [])
    (hC : C+2≤R) (hd : depth+1≤R) (hcap : Completion.SourceDigitWidth.capacity (2*M)≤R) :
    Step initializeLiteral (initializeLiteralFuel C R M)
      (Fin.addCases (m:=298) (n:=1) (motive:=fun _=>Nat) (levelH (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1)) (coldData C R fields extra)
      (Fin.addCases (m:=298) (n:=1) (motive:=fun _=>Nat) (levelH (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
      (bootData C R M depth (Function.update fields 106 (PacketVector.bank R (List.replicate C []))) extra) := by
  have first:=VectorNumericArena.initialize_dense_run R C (coldData C R fields extra) hC rfl rfl h.bank rfl
  rw [initialized_heads,cold_data_update_bank] at first
  have second:=initialize_cold_run C R M root depth p _ extra
    (cold_state_bank C R M root depth p fields extra [] _ h) (by omega) (by omega) hd hcap
  exact first.seq second

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp

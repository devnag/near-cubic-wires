import Proof.Packets.PacketsXWindowEmittedLayout

/-! Complete fixed per-child provider: allocate/reset private words, generate
and execute the actual nested window stream, then close, rename and normalize
it. Atom substitution is applied only after the whole literal vector. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open CloseoutRowsRawPairSeek (cacheWord)
open NormalizedFiniteTransport WindowNativeOrder Theorem25Completion.CycleBounds

attribute [local irreducible] Workspace.machine seedEmit literalConsume
noncomputable def literalProvider := Composition.machine Workspace.machine
  (Composition.machine seedEmit literalConsume)
def literalProviderBudget (C R v u M offset W target : Nat) (codes : List Nat) :=
  (2*R+4)+1+(WindowSeed.completeBudget R v u M W+1+
    literalConsumeBudget C R codes v offset (2*W) target)
noncomputable def literalProviderOutput (C R v u offset W target : Nat) (codes : List Nat)
    (A : Fin 256→ List Bool) :=
  completed R ((Normalized.structuralGF2ConsecutiveWindowIndicator codes offset (2*W) target).map (maskNat C))
    (emittedOutput R v u codes.length offset W target (Workspace.cleared R A))

theorem seed_workspace_away : ∀i,¬Workspace.selected (seedPorts i) := by decide

theorem literal_provider_run (C w v u offset W target : Nat) (codes : List Nat)
    (hc : codes.Pairwise (·<·)) (hcodes : ∀c∈codes,c< C) (hsize : codes.length≤ C)
    (hMv : codes.length≤2^v) (hw : 3≤ w) (hdegree : 2*W+1≤2^w)
    (hcount : (codes.length+1)^(2*W)≤2^w)
    (left : List (List Bool)) (A : Fin 256→ List Bool)
    (hengine : ∀i : Fin 34,A (i.castAdd 222)=ReusableArithmetic.state C (commonReserve C w) left [] i)
    (acache : A 186=ZeroPadding.pad (commonReserve C w) (cacheWord (literalPairs codes)))
    (hwork : ∀i,Workspace.selected i→(A i).length≤ commonReserve C w)
    (hu : 2*u+1≤ commonReserve C w) (hv : 2*v+1≤ commonReserve C w)
    (hmeta : ∀j : Fin 7,A (seedPorts (Fin.natAdd 62 j))=
      WindowSeed.metadata (commonReserve C w) v u codes.length offset W target j)
    (hprivate : ∀j,(A (seedPorts (WindowSeed.privateSlot j))).length≤ commonReserve C w)
    (hfit : offset+2*W<2^u) (hd : 2*W+1<2^u) (ht : target<2^u)
    (hfields : 2*v+2*W+3≤ commonReserve C w)
    (hC : ∀k≤2*W,CloseoutRowsModeElementary.budget v k codes.length+1≤ commonReserve C w) :
    Step literalProvider
      (literalProviderBudget C (commonReserve C w) v u codes.length offset W target codes)
      heads A heads (literalProviderOutput C (commonReserve C w) v u offset W target codes A) := by
  let R:=commonReserve C w
  let B:=Workspace.cleared R A
  let E:=emittedOutput R v u codes.length offset W target B
  have ar : A 32=List.replicate R true:=hengine 32
  have al : A 33=List.replicate (R+3) false:=hengine 33
  have first:=Workspace.run R heads A workspace_heads ar al hwork
  have hunchanged : ∀i,B (seedPorts i)=A (seedPorts i) := by
    intro i
    exact if_neg (seed_workspace_away i)
  have hR : C+2≤ R:=LiteralCacheReuse.reserve_width C w
  have middle:=seed_emitted_run R v u codes.length offset W target heads B seed_heads hu hv (by omega) hMv
    ((Workspace.core_retained R A 32).trans ar) ((Workspace.core_retained R A 33).trans al)
    (fun j=>(hunchanged _).trans (hmeta j)) (fun j=>by rw [hunchanged];exact hprivate j)
    hfit hd ht hfields hC
  have hsource : emittedHeads v codes.length offset W target heads 78=
      ((positionalWindow v codes.length offset (2*W) target).flatMap ExtIncidence.monomialWord).length := by
    simp only [emittedHeads,Function.update_of_ne (by decide : (78 : Fin 256)≠95),Function.update_self]
    rw [WindowSeed.emitted_word]
  have houter : emittedHeads v codes.length offset W target heads 95=1 := by simp [emittedHeads]
  have last:=literal_consume_run C w codes hc hcodes hsize v offset (2*W) target hMv hw hdegree hcount
    (emittedHeads v codes.length offset W target heads) E hsource houter (consume_raw_heads v codes.length offset W target)
    (emitted_raw_ready C R v u offset W target codes left A hengine acache
      (positional_stream_guard C w codes hsize hc v offset (2*W) target hMv hdegree hcount))
    (consume_native_heads v codes.length offset W target) (emitted_native C R v u codes.length offset W target left A hengine)
  rw [consume_final_heads] at last
  simpa only [literalProvider,literalProviderBudget,literalProviderOutput,R,B,E] using first.seq (middle.seq last)

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider

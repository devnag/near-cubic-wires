import Proof.Packets.PacketsXWindowConsume

/-! Per-child literal windows are normalized before vector construction.
Substitution is deliberately deferred until the full vector coordinate has
been constructed, matching the frozen ordered-polynomial definition. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open CloseoutRowsRawPairSeek (cacheWord)
open NormalizedFiniteTransport WindowNativeOrder Theorem25Completion.CycleBounds

attribute [local irreducible] closeSource renameNormalize lower
noncomputable def literalConsume := Composition.machine closeSource (Composition.machine renameNormalize lower)
def literalBudget (C R : Nat) (codes : List Nat) (v offset width target : Nat) :=
  RawSingletonSubstitution.budget (literalPairs codes) width
    (positionalWindow v codes.length offset width target).length+1+
    ReusableNative.budget (NativeNormalized.budget C (renamed codes v offset width target)) R
def literalConsumeBudget (C R : Nat) (codes : List Nat) (v offset width target : Nat) :=
  2*R+4+1+(literalBudget C R codes v offset width target+2)

theorem literal_consume_run (C w : Nat) (codes : List Nat) (hc : codes.Pairwise (·<·))
    (hcodes : ∀c∈codes,c<C) (hsize : codes.length≤C) (v offset width target : Nat)
    (hM : codes.length≤2^v) (hw : 3≤w) (hd : width+1≤2^w)
    (hcount : (codes.length+1)^width≤2^w)
    (H : Fin 256→Nat) (A : Fin 256→List Bool)
    (hsource : H 78=((positionalWindow v codes.length offset width target).flatMap ExtIncidence.monomialWord).length)
    (houter : H 95=1)
    (hh : ∀i,Function.update H 78 0 (rawPorts i)=0)
    (ha : ∀i,A (rawPorts i)=RawSingletonSubstitution.bank (commonReserve C w)
      (ExtIncidence.stream (positionalWindow v codes.length offset width target))
      (ZeroPadding.pad (commonReserve C w) (cacheWord (literalPairs codes))) [] i)
    (hn : ∀i,ReusableNative.heads i=Function.update H 78 0 (nativePorts i))
    (an : ∀i,A (nativePorts i)=ReusableNative.ready C (commonReserve C w) [] i) :
    Step literalConsume (literalConsumeBudget C (commonReserve C w) codes v offset width target)
      H A (Function.update (Function.update H 78 0) 95 0)
      (completed (commonReserve C w)
        ((Normalized.structuralGF2ConsecutiveWindowIndicator codes offset width target).map (maskNat C)) A) := by
  have hstream:=positional_stream_guard C w codes hsize hc v offset width target hM hd hcount
  have hbody : ((positionalWindow v codes.length offset width target).flatMap ExtIncidence.monomialWord).length+1≤commonReserve C w := by
    simpa only [ExtIncidence.stream,List.length_append,List.length_singleton] using hstream
  have a78 : A 78=ZeroPadding.pad (commonReserve C w)
      (((positionalWindow v codes.length offset width target).flatMap ExtIncidence.monomialWord)++[false]) := ha 0
  have h31 : H 31=1 := by simpa [nativePorts,ReusableNative.heads] using (hn 33).symm
  have a31 : A 31=UnaryTemplate.tape (commonReserve C w) := an 33
  have first:=close_existing _ _ H A hsource a78 h31 a31 hbody
  have hR : 1≤commonReserve C w := by
    unfold commonReserve
    have := Nat.one_le_pow (8*w) 2 (by decide)
    have := Nat.one_le_pow 4 (C+1) (by omega)
    nlinarith
  have hC : C≤commonReserve C w := by
    unfold commonReserve
    have hp : C≤(C+1)^4 := by nlinarith [(Nat.le_pow (a:=C+1) (by omega : 0<4))]
    have ht := Nat.one_le_pow (8*w) 2 (by decide)
    nlinarith
  have raw:=raw_fuel_guard C w codes hw hsize hcodes hc v offset width target hM hd hcount
  have native:=native_guards C w codes hsize hcodes hc v offset width target hM hd hcount
  have middle:=window_run C (commonReserve C w) codes hc hcodes v offset width target hM hR hC
    (raw_space_guard C w codes hw hsize hcodes width hd) (by omega)
    (Function.update H 78 0) A hh ha hn an native.1 native.2
  have last:=PhysicalIndexReload.move_run (95 : Fin 256) .left (Function.update H 78 0)
    (completed (commonReserve C w)
      ((Normalized.structuralGF2ConsecutiveWindowIndicator codes offset width target).map (maskNat C)) A)
  have h95 : HeadMove.apply .left (Function.update H 78 0 95)=0 := by simp [houter,HeadMove.apply]
  rw [h95] at last
  simpa only [literalConsume,literalConsumeBudget,literalBudget,lower] using first.seq (middle.seq last)

theorem literal_consume_budget (C w : Nat) (codes : List Nat) (hc : codes.Pairwise (·<·))
    (hcodes : ∀c∈codes,c<C) (hsize : codes.length≤C) (v offset width target : Nat)
    (hM : codes.length≤2^v) (hw : 3≤w) (hd : width+1≤2^w)
    (hcount : (codes.length+1)^width≤2^w) :
    literalConsumeBudget C (commonReserve C w) codes v offset width target≤13*commonReserve C w := by
  have raw:=raw_fuel_guard C w codes hw hsize hcodes hc v offset width target hM hd hcount
  have native:=(native_guards C w codes hsize hcodes hc v offset width target hM hd hcount).2
  have large : 65536≤commonReserve C w := by
    unfold commonReserve
    have := Nat.one_le_pow (8*w) 2 (by decide)
    have := Nat.one_le_pow 4 (C+1) (by omega)
    nlinarith
  unfold literalConsumeBudget literalBudget RawSingletonSubstitution.budget ReusableNative.budget
  omega

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider

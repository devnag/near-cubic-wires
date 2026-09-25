import Proof.Packets.PacketsXWindowNativeTyped
import Proof.Packets.PacketsXWindowPositionalSupport
import Proof.Packets.PacketsXCycleRawSingletonGuard
import Proof.Packets.PacketsXCycleNativeNormalizedCost

/-! All raw renaming and native-normalization space/fuel guards follow from
the actual population, degree policy and source census. No extra power of the
literal code width is introduced by the provider. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.ExtDecompositionBatch
open CloseoutRowsRawPairSeek (cacheWord)
open WindowNativeOrder NormalizedFiniteTransport Theorem25Completion

theorem renamed_map (codes : List Nat) (v offset width target : Nat) (hM : codes.length≤2^v) :
    renamed codes v offset width target=
      (positionalWindow v codes.length offset width target).map (List.map (SubsetOrder.lookup codes.reverse)) :=
  (renamed_window codes v offset width target hM).trans (reflected_window codes v offset width target).symm

theorem renamed_count (codes : List Nat) (v offset width target : Nat) (hM : codes.length≤2^v) :
    (renamed codes v offset width target).length=(positionalWindow v codes.length offset width target).length := by
  rw [renamed_map codes v offset width target hM,List.length_map]

theorem renamed_degree_population (codes : List Nat) (v offset width target : Nat) (hM : codes.length≤2^v) :
    ∀m∈renamed codes v offset width target,m.length≤codes.length := by
  rw [renamed_map codes v offset width target hM]
  intro m hm
  obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hm
  simpa only [List.length_map] using window_monomial_length v codes.length offset width target hM a ha

theorem literal_cache_length (C : Nat) (codes : List Nat) (hc : ∀ c∈codes,c<C) :
    (cacheWord (literalPairs codes)).length≤codes.length*(C+6) := by
  simp only [cacheWord,literalPairs,List.flatMap_map]
  change (codes.reverse.flatMap ReflectedLiteralCache.singletonWord).length≤_
  have h:=WindowHomogeneousOrder.length_flatMap_le codes.reverse ReflectedLiteralCache.singletonWord (C+6)
    (by intro c h;rw [ReflectedLiteralCache.singletonWord_length];have h':=hc c (List.mem_reverse.mp h);omega)
  simpa only [List.length_reverse] using h

theorem raw_space_guard (C w : Nat) (codes : List Nat) (hw : 3≤w) (hsize : codes.length≤C)
    (hc : ∀ c∈codes,c<C) (width : Nat) (hd : width+1≤2^w) :
    CloseoutRowsEstimator.SubstitutionBounds.space (literalPairs codes) 1 width
      (cacheWord (literalPairs codes)).length≤CycleBounds.commonReserve C w := by
  rw [CycleRawSingletonCost.space_eq,literalPairs_length]
  exact CycleRawSingletonBudget.space_reserve C w _ codes.length width hw hsize
    (literal_cache_length C codes hc) hd

theorem raw_fuel_guard (C w : Nat) (codes : List Nat) (hw : 3≤w) (hsize : codes.length≤C)
    (hc : ∀ c∈codes,c<C) (hp : codes.Pairwise (·<·)) (v offset width target : Nat)
    (hM : codes.length≤2^v) (hd : width+1≤2^w) (hcount : (codes.length+1)^width≤2^w) :
    CloseoutRowsEstimator.SubstitutionBounds.fuel (literalPairs codes) 1 width
      (positionalWindow v codes.length offset width target).length≤CycleBounds.commonReserve C w := by
  rw [CycleRawSingletonCost.fuel_eq,literalPairs_length]
  exact CycleRawSingletonBudget.fuel_reserve C w _ codes.length width _ hw hsize
    (literal_cache_length C codes hc) hd (window_raw_count codes hp v offset width target w hM hd hcount)

theorem native_guards (C w : Nat) (codes : List Nat) (hsize : codes.length≤C)
    (hc : ∀ c∈codes,c<C) (hp : codes.Pairwise (·<·)) (v offset width target : Nat)
    (hM : codes.length≤2^v) (hd : width+1≤2^w) (hcount : (codes.length+1)^width≤2^w) :
    (∀ i,(NativeNormalized.A C (renamed codes v offset width target) [] i).length≤CycleBounds.commonReserve C w) ∧
    NativeNormalized.budget C (renamed codes v offset width target)+3≤CycleBounds.commonReserve C w := by
  have fits:=renamed_fits C codes hp hc v offset width target hM
  have degree : ∀m∈renamed codes v offset width target,m.length≤C :=
    fun m hm=>(renamed_degree_population codes v offset width target hM m hm).trans hsize
  have count : (renamed codes v offset width target).length≤2^(2*w) := by
    rw [renamed_count codes v offset width target hM]
    exact window_raw_count codes hp v offset width target w hM hd hcount
  exact ⟨CycleBounds.native_input_reserve C w _ fits degree count,
    CycleBounds.native_budget_reserve C w _ fits degree count⟩

theorem positional_stream_guard (C w : Nat) (codes : List Nat) (hsize : codes.length≤C)
    (hp : codes.Pairwise (·<·)) (v offset width target : Nat)
    (hM : codes.length≤2^v) (hd : width+1≤2^w) (hcount : (codes.length+1)^width≤2^w) :
    (ExtIncidence.stream (positionalWindow v codes.length offset width target)).length≤CycleBounds.commonReserve C w := by
  have fits : ∀m∈positionalWindow v codes.length offset width target,∀c∈m,c<C :=
    fun m hm c hcm=>lt_of_lt_of_le ((window_bounds v codes.length offset width target hM m hm).2 c hcm) hsize
  have degree : ∀m∈positionalWindow v codes.length offset width target,m.length≤C :=
    fun m hm=>(window_monomial_length v codes.length offset width target hM m hm).trans hsize
  have h:=CycleBounds.native_input_reserve C w _ fits degree
    (window_raw_count codes hp v offset width target w hM hd hcount) 30
  exact h

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider

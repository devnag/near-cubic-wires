import Proof.CaseAnalysis.RowsModeCacheDelta
import Proof.CaseAnalysis.RowsModeCacheTerms
import Proof.Packets.DenseAtomMeaning
import Proof.Packets.PacketsXLiteralAtomNormalize
import Proof.Packets.PacketsXNormalizedFiniteTransport

/-! Exact natural-code meaning of the physically generated mode-pair cache.
The terminal cache uses tag0; the concatenated sibling/child cache uses
level+1. Both keep original occurrence order and original Nat.pair codes. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DenseLiteralAtomMeaning
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierWalkBridge CloseoutRowsModeCache NormalizedFiniteTransport
open CloseoutRowsRawPairSeek (Pair)

@[simp] theorem pairs_length (mode : Fin 3) (p : Parameters) (count : Nat) :
    (pairs mode p count).length=count := by simp [pairs]
theorem pair_at (mode : Fin 3) (p : Parameters) (count i : Nat) (hi : i<count) :
    (pairs mode p count).getD i ([],[])=
      CloseoutRowsModeLiteralPair.pair (literalState mode p i).neg (literalState mode p i).var i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [pairs]
theorem polynomial_at (mode : Fin 3) (p : Parameters) (count i : Nat) (hi : i<count) :
    ((pairs mode p count).getD i ([],[])).1++((pairs mode p count).getD i ([],[])).2=
      CloseoutRowsModeLiteralMeaning.polynomial (literalState mode p i).neg
        (literalState mode p i).var (literalState mode p i).index := by
  rw [pair_at mode p count i hi]
  rfl

theorem delta_raw (population active depth workspace : Nat) (mask : Finset (Fin population))
    (seed : ToeplitzSeed (canonicalGradedRank population active)) (hd : depth≤canonicalGradedRank population active)
    (level : Fin depth) (i : Nat) (hi : i<2*population) :
    let p:=parameters population active level.val workspace mask seed
    let cs:=pairs 1 p population++pairs 2 p population
    (cs.getD i ([],[])).1++(cs.getD i ([],[])).2=
      structuralListLiteralAtom (depth:=depth) mask (canonicalGradedLabel population active) seed
        (Nat.pair (level.val+1) i) := by
  dsimp only
  have he : decodeListLiteralVariable depth population (Nat.pair (level.val+1) i)=
      some (.delta level ⟨i,hi⟩) := decodeListLiteralVariable_encode (.delta level ⟨i,hi⟩)
  rw [structuralListLiteralAtom,he]
  have hl : level.val<canonicalGradedRank population active:=level.isLt.trans_le hd
  by_cases hleft : i<population
  · rw [List.getD_append _ _ _ _ (by simpa using hleft),polynomial_at _ _ _ i hleft]
    simp only [decodeListLiteralSlot,dif_pos hleft]
    simpa only [decide_eq_true_eq,literalState,snapshot] using sibling_atom population active level.val workspace mask seed (snapshot i) hleft hl
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hleft),pairs_length]
    rw [polynomial_at _ _ _ (i-population) (by omega)]
    simp only [decodeListLiteralSlot,dif_neg hleft]
    simpa only [decide_eq_true_eq,literalState,snapshot] using child_atom population active level.val workspace mask seed
      (snapshot (i-population)) (by change i-population<population;omega) hl


end PCJ9eff70d512234a4c_Fixed.Materializer.DenseLiteralAtomMeaning

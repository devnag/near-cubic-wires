import Proof.Packets.NormalizedVector
import Proof.Packets.VectorTerminalZero
import Proof.Packets.PacketsXNormalizedRing

/-! With frozen terminal width zero, the completed literal vector uses only
valid positive delta tags. Terminal tag-zero atoms are never substituted. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorLiteralSupport
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierListPolynomial

def Supports (p : Nat→Prop) (P : Ring.Poly Nat) : Prop := ∀m∈P,∀x∈m,p x

theorem zero (p : Nat→Prop) : Supports p [] := by simp [Supports]
theorem one (p : Nat→Prop) : Supports p [[]] := by simp [Supports]

theorem norm {p : Nat→Prop} {P : Ring.Poly Nat} (hP : Supports p P) : Supports p (Ring.norm P) := by
  apply Ring.fold_toggle_property (fun m=>∀x∈m,p x) Ring.canon P []
  · simp
  · intro m hm x hx;exact hP m hm x (Ring.canon_mem.mp hx)

theorem add {p : Nat→Prop} {P Q : Ring.Poly Nat} (hP : Supports p P) (hQ : Supports p Q) :
    Supports p (Ring.add P Q) := Ring.fold_toggle_property (fun m=>∀x∈m,p x) id Q P hP hQ

theorem mul {p : Nat→Prop} {P Q : Ring.Poly Nat} (hP : Supports p P) (hQ : Supports p Q) :
    Supports p (Ring.mul P Q) := by
  unfold Ring.mul
  have aux (A : Ring.Poly Nat) (hA : Supports p A) :
      Supports p (P.foldl (fun acc m=>Q.foldl (fun acc n=>Ring.toggle (Ring.canon (m++n)) acc) acc) A) := by
    induction P generalizing A with
    | nil=>exact hA
    | cons m P ih=>
      apply ih
      · intro n hn;exact hP n (by simp [hn])
      · apply Ring.fold_toggle_property (fun m=>∀x∈m,p x) (fun n=>Ring.canon (m++n)) Q A hA
        intro n hn x hx
        rcases List.mem_append.mp (Ring.canon_mem.mp hx) with hm|hnx
        · exact hP m (by simp) x hm
        · exact hQ n hn x hnx
  exact aux [] (zero p)

theorem scale {p : Nat→Prop} {P : Ring.Poly Nat} (c : ZMod 2) (hP : Supports p P) :
    Supports p (structuralGF2Scale c P) := by
  unfold structuralGF2Scale
  split
  · exact zero p
  · exact hP

theorem sum {p : Nat→Prop} {ps : List (Ring.Poly Nat)} (hs : ∀P∈ps,Supports p P) :
    Supports p (Normalized.structuralGF2Sum ps) := by
  have aux (A : Ring.Poly Nat) (hA : Supports p A) : Supports p (ps.foldl Ring.add A) := by
    induction ps generalizing A with
    | nil=>exact hA
    | cons P ps ih=>
      exact ih (fun Q hQ=>hs Q (by simp [hQ])) _ (add hA (hs P (by simp)))
  exact aux [] (zero p)

theorem elementary {p : Nat→Prop} (codes : List Nat) (k : Nat) (hc : ∀x∈codes,p x) :
    Supports p (Normalized.structuralGF2ElementarySymmetric codes k) := by
  apply norm
  intro m hm x hx
  exact hc x ((List.mem_sublistsLen.mp hm).1.subset hx)

theorem shifted {p : Nat→Prop} (codes : List Nat) (offset degree : Nat) (hc : ∀x∈codes,p x) :
    Supports p (Normalized.structuralGF2ShiftedElementarySymmetric codes offset degree) := by
  apply sum
  intro P hP
  obtain ⟨indices,_,rfl⟩:=List.mem_map.mp hP
  exact scale _ (elementary codes _ hc)

theorem window {p : Nat→Prop} (codes : List Nat) (offset width target : Nat) (hc : ∀x∈codes,p x) :
    Supports p (Normalized.structuralGF2ConsecutiveWindowIndicator codes offset width target) := by
  apply sum
  intro P hP
  obtain ⟨degree,_,rfl⟩:=List.mem_map.mp hP
  exact scale _ (shifted codes _ _ hc)

/-- A valid delta code carries an actual level and an actual literal slot. -/
def DeltaCode (depth population code : Nat) : Prop :=
  ∃level : Fin depth,∃slot : Fin (2*population),code=Nat.pair (level.val+1) slot.val

theorem delta_codes {depth population : Nat} (level : Fin depth) :
    ∀x∈deltaLiteralVariableCodes (population:=population) level,DeltaCode depth population x := by
  intro x hx
  obtain ⟨slot,rfl⟩:=List.mem_ofFn.mp hx
  exact ⟨level,slot,rfl⟩

theorem factor {rank depth population : Nat} (label : Fin population→BinaryVector rank)
    (seed : ToeplitzSeed rank) (wins : Fin depth→Nat) (level : Fin depth)
    (parent child : Fin (population+1)) :
    Supports (DeltaCode depth population) (Normalized.structuralDeltaFactor label seed wins level parent child) := by
  unfold Normalized.structuralDeltaFactor
  dsimp only
  split
  · exact zero _
  · exact window _ _ _ _ (delta_codes level)

theorem getD {p : Nat→Prop} {ps : List (Ring.Poly Nat)} (hs : ∀P∈ps,Supports p P) (i : Nat) :
    Supports p (ps.getD i []) := by
  by_cases hi:i<ps.length
  · simpa [List.getD,List.getElem?_eq_getElem,hi] using hs ps[i] (List.getElem_mem hi)
  · simp [List.getD,List.getElem?_eq_none (by omega : ps.length ≤ i),zero]

theorem level {rank depth population : Nat} (label : Fin population→BinaryVector rank)
    (seed : ToeplitzSeed rank) (wins : Fin depth→Nat) (j : Fin depth) (ps : List (Ring.Poly Nat))
    (hs : ∀P∈ps,Supports (DeltaCode depth population) P) :
    ∀P∈NormalizedVector.level label seed wins j ps,Supports (DeltaCode depth population) P := by
  intro P hP
  obtain ⟨parent,rfl⟩:=List.mem_ofFn.mp hP
  apply sum
  intro Q hQ
  obtain ⟨child,rfl⟩:=List.mem_ofFn.mp hQ
  exact mul (getD hs child.val) (factor label seed wins j parent child)

theorem table {rank depth population : Nat} (label : Fin population→BinaryVector rank)
    (seed : ToeplitzSeed rank) (wins : Fin depth→Nat) (n : Nat) :
    ∀P∈NormalizedVector.table label seed wins 0 n,Supports (DeltaCode depth population) P := by
  induction n with
  | zero=>
    intro P hP
    obtain ⟨candidate,rfl⟩:=List.mem_ofFn.mp hP
    rw [VectorTerminal.terminal_zero]
    split
    · exact one _
    · exact zero _
  | succ n ih=>
    rw [NormalizedVector.table]
    split
    · exact level label seed wins _ _ ih
    · exact ih

theorem coordinate {rank depth population : Nat} (label : Fin population→BinaryVector rank)
    (seed : ToeplitzSeed rank) (wins : Fin depth→Nat) (candidate : Fin (population+1)) :
    Supports (DeltaCode depth population)
      (Normalized.structuralListPolynomialVector label seed wins 0 candidate) := by
  rw [←NormalizedVector.build_coordinate label seed wins 0 candidate]
  exact getD (table label seed wins depth) candidate.val

end PCJ9eff70d512234a4c_Fixed.Materializer.VectorLiteralSupport

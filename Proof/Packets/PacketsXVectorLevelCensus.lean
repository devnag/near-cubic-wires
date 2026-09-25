import Proof.Packets.PacketsXVectorParentExact

/-! The actual descending vector levels satisfy the literal alphabet and
degree guards, with the original planner census unchanged. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierListPolynomial NearCubicWires.RepairSource.CloseoutRawRows
open NormalizedIntermediate

theorem raw_degree_antitone {depth : Nat} (wins : Fin depth→Nat) (terminal : Nat) :
    Antitone (structuralListCoordinateRawDegreeFrom depth wins terminal) := by
  apply antitone_nat_of_succ_le
  intro level
  by_cases hl:level<depth
  · conv_rhs=>rw [structuralListCoordinateRawDegreeFrom,dif_pos hl]
    omega
  · rw [structuralListCoordinateRawDegreeFrom,dif_neg (by omega : ¬level+1<depth),
      structuralListCoordinateRawDegreeFrom,dif_neg hl]

theorem level_degree_split {depth : Nat} (wins : Fin depth→Nat) (done d : Nat) (hd:done<depth)
    (hdegree:structuralListCoordinateRawDegree depth wins 0≤d) :
    structuralListCoordinateRawDegreeFrom depth wins 0 (depth-done)+
        2*wins ⟨depth-(done+1),by omega⟩≤d := by
  have hbase:structuralListCoordinateRawDegreeFrom depth wins 0 (depth-(done+1))≤d :=
    (raw_degree_antitone wins 0 (Nat.zero_le _)).trans hdegree
  rw [structuralListCoordinateRawDegreeFrom,dif_pos (by omega : depth-(done+1)<depth)] at hbase
  have he:depth-(done+1)+1=depth-done:=by omega
  simpa only [he] using hbase

theorem level_table_bounded {rank depth population : Nat}
    (label : Fin population→BinaryVector rank) (seed : ToeplitzSeed rank) (wins : Fin depth→Nat)
    (done : Nat) (hd:done≤depth) :
    ∀P∈NormalizedVector.table label seed wins 0 done,
      Bounded (LiteralAlphabet.codes depth population)
        (structuralListCoordinateRawDegreeFrom depth wins 0 (depth-done)) P := by
  rw [NormalizedVector.table_exact label seed wins 0 done hd]
  intro P hP
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hP
  exact ⟨LiteralAlphabet.good_vectorFrom label seed wins 0 (depth-done) i,
    Normalized.degree_structuralListPolynomialVectorFrom label seed wins 0 (depth-done) i⟩

theorem level_delta_bounded {rank depth population : Nat}
    (label : Fin population→BinaryVector rank) (seed : ToeplitzSeed rank) (wins : Fin depth→Nat)
    (level : Fin depth) (parent child : Nat) (hp:parent<population+1) (hc:child<population+1) :
    Bounded (LiteralAlphabet.codes depth population) (2*wins level)
      (levelDelta label seed wins level parent child) := by
  simp only [levelDelta,dif_pos hp,dif_pos hc]
  exact ⟨LiteralAlphabet.good_delta label seed wins level _ _,Normalized.degree_deltaFactor label seed wins level _ _⟩

theorem literal_census (depth population d w : Nat)
    (hfit:(population*(2*depth+1)+2)^d≤2^w) :
    ((LiteralAlphabet.codes depth population).card+1)^d≤2^w := by
  apply (Nat.pow_le_pow_left (by have h:=LiteralAlphabet.codes_card depth population;omega) d).trans hfit

end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp

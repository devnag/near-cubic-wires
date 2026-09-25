import Proof.Assembly.FixedCore

/-! Exact materialized level vectors for the fixed normalized constructor.
Each update reads the preceding table; no child coordinate is recursively
recomputed. Operand order and every intermediate normalization are preserved. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedVector
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierListPolynomial NearCubicWires.SupplierListSchedule

variable {rank depth population : Nat}
variable (label : Fin population → BinaryVector rank) (seed : ToeplitzSeed rank)
variable (window : Fin depth → Nat) (terminalWindow : Nat)

def terminal : List StructuralGF2Polynomial :=
  List.ofFn (Normalized.structuralTerminalPolynomialVector depth population terminalWindow)

def level (j : Fin depth) (previous : List StructuralGF2Polynomial) : List StructuralGF2Polynomial :=
  List.ofFn (fun parent : Fin (population+1)=>
    Normalized.structuralGF2Sum (List.ofFn (fun child : Fin (population+1)=>
      Normalized.structuralGF2Mul (previous.getD child.val [])
        (Normalized.structuralDeltaFactor label seed window j parent child))))

def table : Nat → List StructuralGF2Polynomial
  | 0=>terminal (depth:=depth) (population:=population) terminalWindow
  | n+1=>if h : n<depth then
      level label seed window ⟨depth-(n+1),by omega⟩ (table n)
    else table n

theorem terminal_length : (terminal (depth:=depth) (population:=population) terminalWindow).length=population+1 :=
  List.length_ofFn

theorem level_length (j : Fin depth) (previous : List StructuralGF2Polynomial) :
    (level label seed window j previous).length=population+1 := List.length_ofFn

theorem table_length (n : Nat) : (table label seed window terminalWindow n).length=population+1 := by
  induction n with
  | zero=>exact terminal_length terminalWindow
  | succ n ih=>
    simp only [table]
    split
    · exact level_length label seed window _ _
    · exact ih

theorem level_exact (j : Fin depth) (previous : Fin (population+1) → StructuralGF2Polynomial) :
    level label seed window j (List.ofFn previous)=
      List.ofFn (Normalized.structuralCombineListLevel label seed window j previous) := by
  unfold level
  apply congrArg List.ofFn
  funext parent
  unfold Normalized.structuralCombineListLevel
  apply congrArg Normalized.structuralGF2Sum
  apply congrArg List.ofFn
  funext child
  simp only [List.getD,List.getElem?_ofFn,child.isLt,↓reduceDIte,Option.getD_some]

/-- After n complete level updates, the materialized table is exactly the
original recursive constructor at level depth-n, including list ordering. -/
theorem table_exact (n : Nat) (hn : n≤depth) :
    table label seed window terminalWindow n=
      List.ofFn (Normalized.structuralListPolynomialVectorFrom label seed window terminalWindow (depth-n)) := by
  induction n with
  | zero=>
    simp only [table,terminal,Nat.sub_zero,Normalized.structuralListPolynomialVectorFrom,
      Nat.lt_irrefl,↓reduceDIte]
  | succ n ih=>
    have hnd : n<depth := by omega
    rw [table,dif_pos hnd,ih (by omega),level_exact]
    have hlevel : depth-(n+1)<depth := by omega
    conv_rhs=>rw [Normalized.structuralListPolynomialVectorFrom,dif_pos hlevel]
    have hnxt : depth-(n+1)+1=depth-n := by omega
    rw [hnxt]

def build : List StructuralGF2Polynomial := table label seed window terminalWindow depth

theorem build_exact :
    build label seed window terminalWindow=
      List.ofFn (Normalized.structuralListPolynomialVector label seed window terminalWindow) := by
  simpa only [build,Nat.sub_self,Normalized.structuralListPolynomialVector] using
    table_exact label seed window terminalWindow depth (Nat.le_refl _)

theorem build_coordinate (candidate : Fin (population+1)) :
    (build label seed window terminalWindow).getD candidate.val []=
      Normalized.structuralListPolynomialVector label seed window terminalWindow candidate := by
  rw [build_exact]
  simp only [List.getD,List.getElem?_ofFn,candidate.isLt,↓reduceDIte,Option.getD_some]

end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedVector

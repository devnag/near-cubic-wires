import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-! Exact ordered positional subset source. `sublists` is the colexicographic
ordering used by the low-digit-first cursor; reflecting its coordinate order
recovers the frozen `sublistsLen` order, without a permutation quotient. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubsetOrder

variable {α : Type}

def colexLen (l : List α) (k : Nat) := l.sublists.filter (fun xs=>xs.length==k)

theorem filter_sublists' (l : List α) (k : Nat) :
    l.sublists'.filter (fun xs=>xs.length==k)=l.sublistsLen k := by
  induction l generalizing k with
  | nil => cases k <;> simp
  | cons a l ih =>
    rw [List.sublists'_cons,List.filter_append,List.filter_map]
    cases k with
    | zero => simp [ih,Function.comp_def]
    | succ k => simpa [Function.comp_def,List.sublistsLen_succ_cons]
        using congrArg₂ List.append (ih (k+1)) (congrArg (List.map (List.cons a)) (ih k))

theorem reflected_colex (l : List α) (k : Nat) :
    (colexLen l.reverse k).map List.reverse=l.sublistsLen k := by
  unfold colexLen
  rw [List.sublists_reverse,List.filter_map]
  simp only [Function.comp_def,List.length_reverse]
  rw [List.map_map]
  simpa [Function.comp_def] using filter_sublists' l k

/-- High-digit-first numeric rank, used only to prove literal ordering. -/
def rank (base : Nat) : List Nat→Nat
  | [] => 0
  | a::as => a*base^as.length+rank base as

theorem rank_lt (base : Nat) (xs : List Nat) (hb : 0<base)
    (hx : ∀ x∈xs,x<base) : rank base xs<base^xs.length := by
  induction xs with
  | nil => simp [rank]
  | cons a as ih =>
    have ha:=hx a (by simp)
    have ht:=ih (fun x h=>hx x (by simp [h]))
    have hp : 0<base^as.length := Nat.pow_pos hb
    simp only [rank,List.length_cons,pow_succ]
    nlinarith

theorem rank_lex_lt (base : Nat) (xs ys : List Nat) (hb : 0<base)
    (hx : ∀ x∈xs,x<base) (hy : ∀ y∈ys,y<base)
    (hlen : xs.length=ys.length) (hlex : List.Lex (·<·) xs ys) :
    rank base xs<rank base ys := by
  induction hlex with
  | @nil b bs => simp at hlen
  | @rel a as b bs hab =>
    have htail : as.length=bs.length := by simpa using hlen
    have ht:=rank_lt base as hb (fun x h=>hx x (by simp [h]))
    have hp : 0<base^as.length := Nat.pow_pos hb
    simp only [rank]
    rw [←htail]
    nlinarith
  | @cons a as bs h ih =>
    have ht : as.length=bs.length := by simpa using hlen
    have hi:=ih (fun x h=>hx x (by simp [h])) (fun x h=>hy x (by simp [h])) ht
    simp only [rank,ht]
    omega

end PCJ9eff70d512234a4c_Fixed.Materializer.SubsetOrder

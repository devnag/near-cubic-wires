import Std.Tactic
set_option autoImplicit false
namespace PCJ9eff70d512234a4c_Fixed.PhysicalMaskIndices
/-- Increasing native child indices selected by an incidence mask. -/
def selectedIndices (offset : Nat) : List Bool → List Nat
  | [] => []
  | bit :: rest => (if bit then [offset] else []) ++ selectedIndices (offset+1) rest
end PCJ9eff70d512234a4c_Fixed.PhysicalMaskIndices

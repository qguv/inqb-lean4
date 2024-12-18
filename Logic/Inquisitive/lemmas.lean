import Logic.Inquisitive.types
import Logic.Inquisitive.ops
import Logic.Inquisitive.projections

namespace Inquisitive.lemmas

variable {W : Type}
variable {p q : Proposition W}

-- TODO maybe make this an iff and tell the `ext` tactic to use it?
theorem eq_of_truthSet_eq : p.truthSet = q.truthSet → p = q := by
  rw [Proposition.mk.injEq]
  simp only [imp_self]

--theorem info_is_double_absolutePseudoComplement : p.info = p.absolutePseudoComplement.absolutePseudoComplement := by
--theorem meet_bottom : p.absolutePseudoComplement.meet p = bottom W := sorry
--theorem join_bottom : p.absolutePseudoComplement.join (bottom W) = p := sorry

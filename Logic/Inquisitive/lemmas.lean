import Logic.Inquisitive.types
import Logic.Inquisitive.ops
import Logic.Inquisitive.projections

namespace Inquisitive.lemmas

-- a.k.a. book exercise 3.6, homework 1 exercise 3
theorem info_is_double_absolutePseudoComplement (p : Proposition W) : p.info.truthSet = p.absolutePseudoComplement.absolutePseudoComplement.truthSet := by
  sorry

-- TODO maybe make this an iff and tell the `ext` tactic to use it?
theorem eq_of_truthSet_eq {p q : Proposition W} : p.truthSet = q.truthSet → p = q := sorry

import Logic.Inquisitive.types
import Logic.Inquisitive.ops
import Logic.Inquisitive.projections
import Logic.Inquisitive.lemmas

namespace Inquisitive

-- a.k.a. book exercise 3.6, homework 1 exercise 3
theorem fact_3_14 (p : Proposition W) : p = Proposition.meet p.info p.decisionSet := by
  let info := p.info
  have h1 := lemmas.info_is_double_absolutePseudoComplement p
  have h2 := Eq.mp (a := p.info) (b := p.absolutePseudoComplement.absolutePseudoComplement) h1 p.info
  rw [h] at p
  have p := p.info.containsEmpty
  sorry

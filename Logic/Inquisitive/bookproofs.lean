import Mathlib

import Logic.Inquisitive.types
import Logic.Inquisitive.ops
import Logic.Inquisitive.projections
import Logic.Inquisitive.lemmas

namespace Inquisitive

variable {W : Type}

#print lemmas.info_is_double_absolutePseudoComplement

-- maybe make this an iff and tell the `ext` tactic to use it?
lemma Proposition.eq_of_truthSet_eq {p q : Proposition W} : p.truthSet = q.truthSet → p = q := sorry

-- a.k.a. book exercise 3.6, homework 1 exercise 3
theorem fact_3_14 (p : Proposition W) : p = p.info.meet p.decisionSet := by
  --let not_info := p.info.truthSetᶜ
  --let px := p
  have h1 := lemmas.info_is_double_absolutePseudoComplement p
  apply Proposition.eq_of_truthSet_eq
  unfold Proposition.meet
  simp
  rw [h1]
  unfold Proposition.absolutePseudoComplement
  simp
  unfold Proposition.decisionSet
  simp
  unfold Proposition.absolutePseudoComplement
  simp
  -- ext turns equalities into bi-implications
  ext x
  constructor
  · intro x_in
    -- simp only is like rw but applies any number of times and in any order
    --simp?
    --show_term simp
    --consider always converting simp to simp only
    --simp only [Set.mem_inter_iff, Set.mem_powerset_iff, Set.mem_union]
    sorry

  ·

    sorry


  -- rcases p with ⟨X, hX, hX'⟩

  -- have h2 := Eq.mp (a := p.info) (b := p.absolutePseudoComplement.absolutePseudoComplement) h1 p.info
  --rw [h1] at p

  -- have p := p.info.containsEmpty
  -- sorry

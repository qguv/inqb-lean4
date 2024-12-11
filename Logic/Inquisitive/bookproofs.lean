import Mathlib

import Logic.Inquisitive.types
import Logic.Inquisitive.ops
import Logic.Inquisitive.projections
import Logic.Inquisitive.lemmas

namespace Inquisitive

variable {W : Type}

#print lemmas.info_is_double_absolutePseudoComplement

-- a.k.a. book exercise 3.6, homework 1 exercise 3
theorem fact_3_14 (p : Proposition W) : p = p.info.meet p.decisionSet := by
  --let not_info := p.info.truthSetᶜ
  --let px := p
  have h1 := lemmas.info_is_double_absolutePseudoComplement p
  apply lemmas.eq_of_truthSet_eq
  unfold Proposition.meet
  simp only
  apply lemmas.eq_of_truthSet_eq at h1
  rw [h1]
  unfold Proposition.absolutePseudoComplement
  simp only
  unfold Proposition.decisionSet
  simp only
  unfold Proposition.absolutePseudoComplement
  simp only
  --simp
  -- ext turns equalities into bi-implications
  ext x
  constructor
  case a.h.mp =>
    intro s
    simp only [Set.mem_inter_iff, Set.mem_powerset_iff, Set.mem_union]
    constructor
    case right => exact Or.inl s
    case left =>
      intro t
      intro h
      rw [Set.mem_compl_iff]
      --rw [Set.not_mem_of_not_mem_sUnion]
      --apply Not.intro
      intro u
      --rw [Set.mem_def]
      sorry
  case a.h.mpr =>
    intro h2
    cases h2.right with
    | inl h3 => exact h3
    | inr h3 =>
      sorry
    -- simp only is like rw but applies any number of times and in any order
    --simp?
    --show_term simp
    --consider always converting simp to simp only
    --simp only [Set.mem_inter_iff, Set.mem_powerset_iff, Set.mem_union]


  -- rcases p with ⟨X, hX, hX'⟩

  -- have h2 := Eq.mp (a := p.info) (b := p.absolutePseudoComplement.absolutePseudoComplement) h1 p.info
  --rw [h1] at p

  -- have p := p.info.containsEmpty
  -- sorry

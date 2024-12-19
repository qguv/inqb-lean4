import Mathlib

import Logic.Inquisitive.types
import Logic.Inquisitive.ops
import Logic.Inquisitive.projections
import Logic.Inquisitive.lemmas
import Logic.Inquisitive.entailment
import Logic.SetLemmas

namespace Inquisitive

variable {W : Type}
variable (p : Proposition W)

-- a.k.a. book exercise 3.6, homework 1 exercise 3
theorem fact_3_14 : p = p.bang.meet p.decisionSet := by

  -- from meet to intersection of truthsets
  unfold Proposition.meet
  apply lemmas.eq_of_truthSet_eq
  simp only

  -- ?p → p ∪ p*
  unfold Proposition.decisionSet
  simp only

  -- distribute ∩ across ∪
  rw [Set.inter_union_distrib_left]

  -- split equality proof into biconditional
  ext x
  constructor

  -- p -> !p ∩ ?p
  case a.h.mp =>
    intro s
    apply Or.inl
    apply And.intro
    case left =>
      unfold Proposition.bang
      simp only
      exact Set.subset_sUnion_of_mem s
    case right =>
      exact s

  -- !p ∩ ?p -> p
  case a.h.mpr =>
    intro s
    cases s with
    | inl h => exact h.right
    | inr h =>
      obtain ⟨info, comp⟩ := h
      unfold Proposition.bang at info
      simp only at info
      rw [Set.mem_powerset_iff] at info
      unfold Proposition.absolutePseudoComplement at comp
      rw [Set.mem_powerset_iff] at comp
      have h := p.containsEmpty
      have h2 := SetLemmas.empty_of_subset_of_compl x info comp
      subst x
      exact h

theorem fact_2_19i (h: ¬p.isInquisitive) : (p.truthSet = 𝒫 p.info) := by
  ext t
  constructor

  -- in any case...
  case h.mp =>
    intro h1

    -- by definition, info(p) = ⋃₀ P, which means that t ∈ 𝒫 info(p)
    rw [Proposition.info]
    rw [Set.mem_powerset_iff]
    exact Set.subset_sUnion_of_mem h1

  -- suppose p is non-inquisitive...
  case h.mpr =>

    -- i.e. suppose info(p) ∈ p
    rw [Proposition.isInquisitive] at h
    rw [Set.not_not_mem] at h

    -- by downward closure, every substate of p.info must be in p as well
    have h2 := p.downwardClosed p.info

    -- so 𝒫 info(p) ⊆ p
    have h3 := h2 h

    rw [Set.subset_def] at h3
    exact h3 t

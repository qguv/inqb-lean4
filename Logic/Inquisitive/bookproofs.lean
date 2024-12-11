import Mathlib

import Logic.Inquisitive.types
import Logic.Inquisitive.ops
import Logic.Inquisitive.projections
import Logic.Inquisitive.lemmas

namespace Inquisitive

variable {W : Type}

-- a.k.a. book exercise 3.6, homework 1 exercise 3
theorem fact_3_14 (p : Proposition W) : p = p.info.meet p.decisionSet := by

  -- from meet to intersection of truthsets
  unfold Proposition.meet
  apply lemmas.eq_of_truthSet_eq
  simp only

  -- from decisionSet to union of self and complement
  unfold Proposition.decisionSet
  simp only

  rw [Set.inter_union_distrib_left]

  ext x
  constructor
  case a.h.mp =>
    intro s
    apply Or.inl
    apply And.intro
    case left =>
      unfold Proposition.info
      simp only
      exact Set.subset_sUnion_of_mem s
    case right =>
      exact s
  case a.h.mpr =>
    intro s
    cases s with
    | inl h => exact h.right
    | inr h =>
      obtain ⟨info, comp⟩ := h
      -- have: x ∈ (!p).truthSet and x ∈ (p*).truthSet
      -- need: !p ∪ p* = p
      -- original idea: use lemma !p = p**
      -- new idea: use p ⊆ !p
      unfold Proposition.info at info
      simp only at info
      rw [Set.mem_powerset_iff] at info
      unfold Proposition.absolutePseudoComplement at comp
      rw [Set.mem_powerset_iff] at comp
      have h := p.containsEmpty
      -- the only way for x to be the subset of a set and its compliment is for it to be the empty set
      -- which we know is in p.truthSet by p.containsEmpty
      sorry

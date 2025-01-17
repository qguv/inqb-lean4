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

-- original proof, absent from book
theorem fact_2_14 : ∀ w, p.trueIn w ↔ p.supportedBy {w} := by
  intro w
  rw [Proposition.trueIn, Proposition.supportedBy, Proposition.info]
  constructor
  case mp =>
    intro h
    rw [Set.mem_sUnion] at h
    obtain ⟨t, ⟨h1, h2⟩⟩ := h
    have dc := p.downwardClosed
    apply dc t h1
    rw [Set.mem_powerset_iff]
    rw [Set.singleton_subset_iff]
    exact h2
  case mpr =>
    intro h
    rw [Set.mem_sUnion]
    constructor
    case w => exact {w}
    case h =>
      constructor
      case left => exact h
      case right => rfl

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

theorem fact_2_19ii (h : p.truthSet = 𝒫 p.info) : ∃ s_max ∈ p.truthSet, ∀ s ∈ p.truthSet, s ⊆ s_max := by
  constructor

  -- info(p)...
  case w => exact p.info

  case h =>
    constructor
    -- is the greatest...
    case right =>
      intro s
      intro h1
      rw [h] at h1
      exact h1

    -- element in p
    case left =>
      rw [h]
      rw [Set.mem_powerset_iff]

theorem fact_2_19iii (h : ∃ s_max ∈ p.truthSet, ∀ s ∈ p.truthSet, s ⊆ s_max) :
  ∀ s : Set W, p.supportedBy s ↔ ∀ w ∈ s, p.trueIn w
:= by
  intro s
  constructor

  -- suppose s supports p...
  case mp =>
    intro h1

    -- i.e. s ∈ p
    rw [Proposition.supportedBy] at h1

    -- by downward closure, {w} ∈ p for all w ∈ s
    intro w
    intro h2
    rw [←Set.singleton_subset_iff] at h2
    have h3 := lemmas.mem_of_subset h1 h2

    -- by fact 2.14, p is true at each w ∈ s
    rw [fact_2_14]
    rw [Proposition.supportedBy]
    exact h3

  -- suppose p is true at each w ∈ s
  case mpr =>
    intro h1

    -- by fact 2.14, this means that {w} ∈ p for all w ∈ s
    conv at h1 =>
      intro
      intro
      rw [fact_2_14]

    -- suppose now that p has a greatest element s_max
    obtain ⟨smax, ⟨h3, h4⟩⟩ := h

    -- then for all w ∈ s, {w} must be included in s_max
    have h5 := fun (w) (w_in_s : w ∈ s) ↦
      h4 {w} (h1 w w_in_s)

    -- and so also s ⊆ s_max
    have h6 := SetLemmas.all_singletons_subsets_implies_subset h5

    -- since s_max ∈ p, it follows by downward closure that s ∈ p
    have h7 := p.downwardClosed smax h3 h6

    -- that is, p is supported at s
    exact h7

theorem fact_2_19iv (h: ∀ s : Set W, p.supportedBy s ↔ ∀ w ∈ s, p.trueIn w) : ¬p.isInquisitive := by
  unfold Proposition.isInquisitive
  push_neg

  -- take any w ∈ p.info ... this shows that p is true at all w ∈ p.info
  have h1 : (∀ w ∈ p.info, p.trueIn w) := by
    intro w
    intro h2

    -- then w ∈ t for some t ∈ p
    obtain ⟨t, h3, w_in_t⟩ := h2

    -- since p is supported by t
    rw [←Proposition.supportedBy] at h3

    -- by h, p is true at w
    have h4 := (h t).mp

    -- since p is supported by t, then by h, p is true at w
    exact h4 h3 w w_in_t

  -- by h, it follows that p is supported by p.info
  have h2 := (h p.info).mpr h1

  -- i.e. that p.info ∈ p
  exact h2

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

import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation
import Logic.Inquisitive.types
import Logic.Inquisitive.lemmas
import Logic.Inquisitive.ops

namespace Inquisitive

def Proposition.info (p : Proposition W) : Proposition W where
  truthSet := 𝒫 ⋃₀ p.truthSet
  containsEmpty := lemmas.emptyset_in_powerset (⋃₀ p.truthSet)
  downwardClosed := lemmas.powerset_downward_closed (⋃₀ p.truthSet)

def Proposition.decisionSet (p : Proposition W) : Proposition W where
  truthSet := p.truthSet ∪ (p.truthSet)ᶜ
  containsEmpty := by
    rw [Set.union_def]
    rw [Set.mem_setOf]
    exact Or.intro_left (∅ ∈ p.truthSetᶜ) p.containsEmpty
  downwardClosed := by
    intro s
    intro h
    rw [Set.union_def] at h
    rw [Set.mem_setOf] at h
    cases h with
    | inl hl =>
      have h2 := p.downwardClosed s hl
      exact Set.subset_union_of_subset_left h2 p.truthSetᶜ
    | inr hr =>
      have h2 := p.downwardClosed s hr
      exact Set.subset_union_of_subset_right h2 p.truthSet
  /-
    intro s
    intro h
    intro t
    rw [Set.union_def] at h
    rw [Set.mem_setOf] at h
    rw [Set.union_def]
    intro h2
    rw [Set.mem_powerset_iff] at h2
    rw [Set.mem_setOf]
    have h := p.downwardClosed
    cases h with
    | inl hl =>
      sorry
    | inr hr =>
      sorry
-/

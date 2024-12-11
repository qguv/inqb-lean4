import Mathlib.Data.Set.Basic
import Logic.SetLemmas

namespace Inquisitive

variable (W : Type)

structure Proposition : Type where
  truthSet : Set (Set W)
  downwardClosed : ∀s ∈ truthSet, 𝒫 s ⊆ truthSet
  containsEmpty : ∅ ∈ truthSet
  --notEmpty : truthSet ≠ ∅

def bottom : Proposition W where
  truthSet := {∅}
  containsEmpty := by
    rw [Set.mem_singleton_iff]
  downwardClosed := by
    intro x
    intro
    intro
    intro h
    subst x
    rw [Set.mem_singleton_iff]
    rw [Set.mem_powerset_iff] at h
    rw [Set.subset_empty_iff] at h
    exact h

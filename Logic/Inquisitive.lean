import Mathlib.Data.Set.Basic

namespace Inquisitive

structure Proposition (W : Type) : Type where
  truthSet : Set (Set W)
  downwardClosure : ∀s ∈ truthSet, 𝒫 s ⊆ truthSet

-- TODO: stop this from polluting namespace
inductive ExW where
| p
| q
| pq
| empty

open ExW

def foo : Proposition ExW where
  truthSet := 𝒫 {p, pq}
  downwardClosure := by
    intro s
    intro h1
    intro x
    intro h2
    intro y
    intro h3
    rw [Set.powerset] at h1
    rw [Set.powerset] at h2
    rw [Set.mem_setOf_eq] at h1
    rw [Set.mem_setOf_eq] at h2
    have h4 := Set.Subset.trans h2 h1
    apply h4
    exact h3

#check Set.Subset

#print foo.proof_1


def Proposition.join (x : Proposition W) (y : Proposition W) : Proposition W where
  truthSet := x.truthSet ∪ y.truthSet
  downwardClosure := by
    intro s
    intro h
    rw [Set.mem_union] at h
    cases h with
    | inl hl =>
      apply Set.subset_union_of_subset_left
      apply x.downwardClosure
      exact hl
    | inr hr =>
      apply Set.subset_union_of_subset_right
      apply y.downwardClosure
      exact hr

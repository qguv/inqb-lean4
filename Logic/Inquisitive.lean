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
    intro _s
    intro h1
    intro _t
    intro h2
    intro _u
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
    intro _s
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

def Proposition.meet (x : Proposition W) (y : Proposition W) : Proposition W where
  truthSet := x.truthSet ∩ y.truthSet
  downwardClosure := by
    intro _s
    intro h
    rw [Set.mem_inter_iff] at h
    apply Set.subset_inter
    case rs =>
      apply x.downwardClosure
      exact h.left
    case rt =>
      apply y.downwardClosure
      exact h.right

def Proposition.relativePseudoComplement (x : Proposition W) : Proposition W where
  truthSet := sorry
  downwardClosure := by
    sorry

def Proposition.absolutePseudoComplement (x : Proposition W) : Proposition W where
  truthSet := {s | ∀t ∈ x.truthSet, s ∩ t = ∅}
  downwardClosure := by
    sorry
    -- intro s
    -- intro h
    -- intro t
    -- intro h2
    -- intro u
    -- intro h3
    -- have h4 := h u h3
    -- rw [Set.powerset, Set.mem_setOf] at h2
    -- -- rw [Set.disjoint_iff_inter_eq_empty] at h4
    -- have h4' : Disjoint s u := sorry
    -- have := Set.disjoint_of_subset_left h2 h4'
    -- apply Set.disjoint_iff_inter_eq_empty

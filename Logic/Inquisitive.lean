import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation

namespace Inquisitive

structure Proposition (W : Type) : Type where
  truthSet : Set (Set W)
  downwardClosure : ∀s ∈ truthSet, 𝒫 s ⊆ truthSet
  containsEmpty : ∅ ∈ truthSet

theorem powerset_downward_closed {α : Type w} (xs : Set α) : (∀ s ∈ 𝒫 xs, 𝒫 s ⊆ 𝒫 xs) := by
  intro
  intro h1
  intro
  intro h2
  intro
  intro h3
  rw [Set.powerset] at h1
  rw [Set.powerset] at h2
  rw [Set.mem_setOf_eq] at h1
  rw [Set.mem_setOf_eq] at h2
  have h4 := Set.Subset.trans h2 h1
  apply h4
  exact h3

-- TODO: stop this from polluting namespace
inductive ExW where
| p
| q
| pq
| empty

open ExW

def foo : Proposition ExW where
  truthSet := 𝒫 {p, pq}
  containsEmpty := by
    rw [Set.mem_powerset_iff]
    exact Set.empty_subset {p, pq}
  downwardClosure := powerset_downward_closed {p, pq}

#print foo.proof_2

def Proposition.join (p : Proposition W) (q : Proposition W) : Proposition W where
  truthSet := p.truthSet ∪ q.truthSet
  containsEmpty := by
    apply Set.mem_union_left
    exact p.containsEmpty
  downwardClosure := by
    intro
    intro h
    rw [Set.mem_union] at h
    cases h with
    | inl hl =>
      apply Set.subset_union_of_subset_left
      apply p.downwardClosure
      exact hl
    | inr hr =>
      apply Set.subset_union_of_subset_right
      apply q.downwardClosure
      exact hr

def Proposition.meet (p : Proposition W) (q : Proposition W) : Proposition W where
  truthSet := p.truthSet ∩ q.truthSet
  containsEmpty := And.intro p.containsEmpty q.containsEmpty
  downwardClosure := by
    intro
    intro h
    rw [Set.mem_inter_iff] at h
    apply Set.subset_inter
    case rs =>
      apply p.downwardClosure
      exact h.left
    case rt =>
      apply q.downwardClosure
      exact h.right

/-
def Proposition.relativePseudoComplement (p : Proposition W) (q : Proposition W) : Proposition W where
  truthSet := {s | ∀ t ⊆ s, t ∈ p → t ∈ q}
  downwardClosure := by
    sorry
-/

def Proposition.absolutePseudoComplement (p : Proposition W) : Proposition W where
  truthSet := 𝒫 (⋃₀ p.truthSet)ᶜ
  containsEmpty := by
    rw [Set.mem_powerset_iff]
    exact Set.empty_subset (⋃₀ p.truthSet)ᶜ
  downwardClosure := powerset_downward_closed (⋃₀ p.truthSet)ᶜ

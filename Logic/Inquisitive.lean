import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation

namespace Inquisitive

structure Proposition (W : Type) : Type where
  truthSet : Set (Set W)
  downwardClosed : ∀s ∈ truthSet, 𝒫 s ⊆ truthSet
  containsEmpty : ∅ ∈ truthSet

theorem subset_trans {α : Type} {A : Set α} {B : Set α} {C : Set α} : A ⊆ B → B ⊆ C → A ⊆ C := by
  intro a_sub_b
  intro b_sub_c
  rw [Set.subset_def] at a_sub_b
  rw [Set.subset_def] at b_sub_c
  rw [Set.subset_def]
  intro x
  intro x_in_a
  have x_in_b := a_sub_b x x_in_a
  have x_in_c := b_sub_c x x_in_b
  exact x_in_c

theorem powerset_downward_closed {α : Type} (xs : Set α) : (∀ s ∈ 𝒫 xs, 𝒫 s ⊆ 𝒫 xs) := by
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
  have h4 := subset_trans h2 h1
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
  downwardClosed := powerset_downward_closed {p, pq}

#print foo.proof_2

def Proposition.join (p : Proposition W) (q : Proposition W) : Proposition W where
  truthSet := p.truthSet ∪ q.truthSet
  containsEmpty := by
    apply Set.mem_union_left
    exact p.containsEmpty
  downwardClosed := by
    intro
    intro h
    rw [Set.mem_union] at h
    cases h with
    | inl hl =>
      apply Set.subset_union_of_subset_left
      apply p.downwardClosed
      exact hl
    | inr hr =>
      apply Set.subset_union_of_subset_right
      apply q.downwardClosed
      exact hr

def Proposition.meet (p : Proposition W) (q : Proposition W) : Proposition W where
  truthSet := p.truthSet ∩ q.truthSet
  containsEmpty := And.intro p.containsEmpty q.containsEmpty
  downwardClosed := by
    intro
    intro h
    rw [Set.mem_inter_iff] at h
    apply Set.subset_inter
    case rs =>
      apply p.downwardClosed
      exact h.left
    case rt =>
      apply q.downwardClosed
      exact h.right

def Proposition.relativePseudoComplement (p : Proposition W) (q : Proposition W) : Proposition W where
  truthSet := {s | ∀ t ⊆ s, t ∈ p.truthSet → t ∈ q.truthSet}
  containsEmpty := by
    intro
    intro b
    intro
    rw [Set.subset_empty_iff] at b
    rw [b]
    exact q.containsEmpty

  downwardClosed := by
    intro
    intro h1
    rw [Set.mem_setOf] at h1
    intro
    intro h2
    rw [Set.mem_setOf]
    intro h3
    intro h4
    rw [Set.mem_powerset_iff] at h2
    have h5 := subset_trans h4 h2
    exact h1 h3 h5

def Proposition.absolutePseudoComplement (p : Proposition W) : Proposition W where
  truthSet := 𝒫 (⋃₀ p.truthSet)ᶜ
  containsEmpty := by
    rw [Set.mem_powerset_iff]
    exact Set.empty_subset (⋃₀ p.truthSet)ᶜ
  downwardClosed := powerset_downward_closed (⋃₀ p.truthSet)ᶜ

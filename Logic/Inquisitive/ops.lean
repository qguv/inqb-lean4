import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation
import Logic.Inquisitive.types
import Logic.SetLemmas

namespace Inquisitive

variable {W: Type}
variable (p q : Proposition W)

def Proposition.join : Proposition W where
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

def Proposition.meet : Proposition W where
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

def Proposition.relativePseudoComplement : Proposition W where
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
    intro t
    intro h3
    rw [Set.mem_powerset_iff] at h2
    have h4 := SetLemmas.subset_trans h3 h2
    exact h1 t h4

def Proposition.absolutePseudoComplement : Proposition W where
  truthSet := 𝒫 (⋃₀ p.truthSet)ᶜ
  containsEmpty := by
    rw [Set.mem_powerset_iff]
    exact Set.empty_subset (⋃₀ p.truthSet)ᶜ
  downwardClosed := SetLemmas.powerset_downward_closed (⋃₀ p.truthSet)ᶜ

import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation

namespace Inquisitive

structure Proposition (W : Type) : Type where
  truthSet : Set (Set W)
  downwardClosure : ∀s ∈ truthSet, 𝒫 s ⊆ truthSet
  containsEmpty : ∅ ∈ truthSet

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
  downwardClosure := by
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

#check Set.Subset

#print foo.proof_2


def Proposition.join (p : Proposition W) (q : Proposition W) : Proposition W where
  truthSet := p.truthSet ∪ q.truthSet
  containsEmpty := by
    apply Set.mem_union_left
    exact p.containsEmpty
  /-
  nonEmpty := by
    have h := Set.union_nonempty (s := p.truthSet) (t := q.truthSet)
    have h2 := Or.inl p.nonEmpty (b := Set.Nonempty q.truthSet)
    rw [←h] at h2
    exact h2
  -/
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
  /-
  nonEmpty := by
    have px := Set.nonempty_def (s := p.truthSet)
    have hp_nonEmpty := p.nonEmpty
    rw [px] at hp_nonEmpty

    have qx := Set.nonempty_def (s := q.truthSet)
    have hq_nonEmpty := q.nonEmpty
    rw [qx] at hq_nonEmpty

    have pq_nonEmpty := And.intro hp_nonEmpty hq_nonEmpty
    rw [Set.inter_nonempty]
    sorry
    -/
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
    /-
    intro s
    have h := Set.inter_empty s
    rw [Set.inter_comm] at h
    intro
    exact h
    -/
  downwardClosure := by
    sorry
    /-
    intro s
    have h1 := p.downwardClosure s
    have h2 := p.containsEmpty
    intro h3
    intro t
    intro u
    intro v
    intro w
    have h4 := h3 ∅
    -/

    /-
    intro s
    intro h1
    intro t
    rw [Set.mem_def] at h1
    have h2 := h1 t
    rw [Set.powerset]
    intro h3
    intro u
    intro h4
    have h5 := h1 u
    -/

    /-
    intro s
    intro h1
    --rw [←Set.mem_powerset_iff]
    --rw [Set.mem_def] at h1
    --rw [Set.mem_powerset_iff]
    --have h2 := h1 ∅
    rw [Set.powerset]
    rw [Set.subset_def]
    intro t
    intro h2
    --have intersection := s ∩ t
    -/

    /-
    intro s
    intro h1
    have h2 := p.containsEmpty
    intro t
    intro h4
    rw [Set.mem_powerset_iff] at h4 -- duplicate of trait subset_of_mem_powerset?
    have h5 := Set.mem_of_mem_of_subset h1 h4
    --apply Set.mem_powerset
    --rw [Set.mem_powerset_iff] at h1
    -/

    /-
    intro s
    intro h1
    have dc := x.downwardClosure
    rw [Set.mem_def] at h1
    -/

    /-
    fun y ↦
    fun h1 ↦
    fun x2 ↦
      let x3 := h1 y
      fun x3 ↦
    -/

    /-
    intro s
    intro h1
    rw [Set.mem_def] at h1
    intro u
    intro h2
    have h3 := h1 u
    have dc := x.downwardClosure
    -/

  /-
    intro s
    intro h1
    intro t
    intro h2
    intro u
    rw [Set.mem_def] at h1
    intro a
    have dc := x.downwardClosure u a
    -/

    /-
    intro s
    intro h
    intro t
    intro h2
    intro u
    intro h3
    have h4 := h u h3
    rw [Set.powerset, Set.mem_setOf] at h2
    -- rw [Set.disjoint_iff_inter_eq_empty] at h4
    have h4' : Disjoint s u := sorry
    have := Set.disjoint_of_subset_left h2 h4'
    apply Set.disjoint_iff_inter_eq_empty
    -/

import Mathlib.Data.Set.Basic

namespace Inquisitive

structure Proposition (W : Type) : Type where
  truthSet : Set (Set W)
  downwardClosure : ∀s ∈ truthSet, 𝒫 s ⊆ truthSet
  nonEmpty : truthSet ≠ ∅

-- TODO: stop this from polluting namespace
inductive ExW where
| p
| q
| pq
| empty

open ExW

def foo : Proposition ExW where
  truthSet := 𝒫 {p, pq}
  nonEmpty := by
    have h := Set.powerset_nonempty (s := {p, pq})
    rw [Set.nonempty_iff_ne_empty] at h
    exact h
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


def Proposition.join (p : Proposition W) (q : Proposition W) : Proposition W where
  truthSet := p.truthSet ∪ q.truthSet
  downwardClosure := by
    intro _s
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
  downwardClosure := by
    intro _s
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

def Proposition.absolutePseudoComplement (x : Proposition W) : Proposition W where
  truthSet := {s | ∀t ∈ x.truthSet, s ∩ t = ∅}
  downwardClosure := by
    intro s
    intro h1
    have dc := x.downwardClosure
    rw [Set.mem_def] at h1
    sorry

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

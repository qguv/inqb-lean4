import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation
import Logic.Inquisitive.types
import Logic.SetLemmas
import Logic.Inquisitive.ops
import Logic.Inquisitive.entailment

namespace Inquisitive

variable {W : Type}
variable (p: Proposition W)

def Proposition.bang : Proposition W where
  truthSet := 𝒫 p.info
  containsEmpty := SetLemmas.emptyset_in_powerset p.info
  downwardClosed := SetLemmas.powerset_downward_closed p.info

def Proposition.decisionSet : Proposition W where
  truthSet := p.truthSet ∪ p.absolutePseudoComplement.truthSet
  containsEmpty := by
    rw [Set.union_def]
    rw [Set.mem_setOf]
    exact Or.intro_left (∅ ∈ p.absolutePseudoComplement.truthSet) p.containsEmpty
  downwardClosed := by
    intro s
    intro h
    rw [Set.union_def] at h
    rw [Set.mem_setOf] at h
    cases h with
    | inl hl =>
      have h2 := p.downwardClosed s hl
      exact Set.subset_union_of_subset_left h2 p.absolutePseudoComplement.truthSet
    | inr hr =>
      have h2 := p.absolutePseudoComplement.downwardClosed s hr
      exact Set.subset_union_of_subset_right h2 p.truthSet

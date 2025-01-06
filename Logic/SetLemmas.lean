import Mathlib.Data.Set.Basic

namespace SetLemmas

variable {α : Type}
variable {A B C: Set α}

theorem subset_trans {B C : Set α}: A ⊆ B → B ⊆ C → A ⊆ C := by
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

-- mathlib complains if I change the definition to this, though they should be equivalent
--theorem powerset_downward_closed : (∀ a ∈ 𝒫 A, 𝒫 a ⊆ 𝒫 A) := by
theorem powerset_downward_closed (xs : Set α) : (∀ s ∈ 𝒫 xs, 𝒫 s ⊆ 𝒫 xs) := by
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

-- mathlib complains if I change the definition to this, though they should be equivalent
--theorem emptyset_in_powerset : (∅ ∈ 𝒫 A) := by
theorem emptyset_in_powerset {α : Type} (xs : Set α) : (∅ ∈ 𝒫 xs) := by
  rw [Set.mem_powerset_iff]
  exact Set.empty_subset xs

theorem empty_of_subset_of_compl : (∀ a ⊆ A, a ⊆ Aᶜ → a = ∅) := by
  -- the only way for x to be the subset of a set and its compliment is for it to be the empty set
  intro h1
  intro h2
  intro h3
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro a
  apply h3
  exact a
  exact h2 a

theorem max_of_powerset : (∀ s ∈ 𝒫 A, s ⊆ A) := by
  intro s
  intro h
  exact h

theorem all_singletons_subsets_implies_subset (h: ∀ a ∈ A, {a} ⊆ B) : (A ⊆ B) :=
  fun a (a_in_a : a ∈ A) ↦
    Set.singleton_subset_iff.mp (h a a_in_a)

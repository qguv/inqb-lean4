import Mathlib.Data.Set.Basic

namespace Inquisitive.lemmas

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

theorem emptyset_in_powerset {α : Type} (xs : Set α) : (∅ ∈ 𝒫 xs) := by
  rw [Set.mem_powerset_iff]
  exact Set.empty_subset xs

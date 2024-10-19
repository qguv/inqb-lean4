import Mathlib.Data.Vector.Defs
import Mathlib.Data.Vector.Basic
-- import Mathlib.Data.Set.Defs
-- import Mathlib.Data.Finset.Basic

open Mathlib

inductive Formula (V : Type) : Type where
| bot : Formula V
| var : V → Formula V
| not : Formula V → Formula V
| or : Formula V → Formula V → Formula V
deriving Repr, DecidableEq

declare_syntax_cat formula

syntax "⊥" : formula
syntax ident : formula
syntax:70 "¬" formula:70 : formula
syntax:50 formula:51 " ∨ " formula:50 : formula
syntax "(" formula ")" : formula
syntax "⟪" term "⟫" : formula

syntax "[f| "  formula " |]" : term

macro_rules
| `([f| ⊥ |]) => `(Formula.bot)
| `([f| $i:ident |]) => `(Formula.var $(Lean.quote (toString i.getId)))
| `([f| ¬$φ:formula |]) => `(Formula.not [f| $φ |])
| `([f| $φ:formula ∨ $ψ:formula |]) => `(Formula.or [f| $φ |] [f| $ψ |])
| `([f| ($φ:formula) |]) => `([f| $φ |])
| `([f| ⟪$t:term⟫ |]) => pure t

#check [f| ¬p ∨ q ∨ ⊥ |]
#check [f| ⟪Formula.or .bot .bot⟫ |]

namespace Formula

abbrev top : Formula V := [f| ¬⊥ |]

syntax "⊤" : formula

macro_rules
| `([f| ⊤ |]) => `(Formula.top)


abbrev and (φ : Formula V) (ψ : Formula V) : Formula V :=
  [f| ¬(¬⟪φ⟫ ∨ ¬⟪ψ⟫) |]

syntax:60 formula:61 " ∧ " formula:60 : formula

macro_rules
| `([f| $φ:formula ∧ $ψ:formula |]) => `(Formula.and [f| $φ |] [f| $ψ |])


abbrev implies (φ : Formula V) (ψ : Formula V) : Formula V :=
  [f| ¬⟪φ⟫ ∨ ⟪ψ⟫ |]

syntax:40 formula:41 " → " formula:40 : formula

macro_rules
| `([f| $φ:formula → $ψ:formula|]) => `(Formula.implies [f| $φ |] [f| $ψ |])


abbrev iff (φ : Formula V) (ψ : Formula V) : Formula V :=
  [f| ⟪φ⟫ → ⟪ψ⟫ ∧ ⟪ψ⟫ → ⟪φ⟫ |]

syntax:30 formula:30 " ↔ " formula:30 : formula

macro_rules
| `([f| $φ:formula ↔ $ψ:formula|]) => `(Formula.iff [f| $φ |] [f| $ψ |])

#check [f| p ∨ q ∧ r |]

end Formula

inductive Subformula (φ : Formula V) : Formula V → Prop where
| eq : φ = ψ → Subformula φ ψ
| not : Subformula φ ψ → Subformula φ (.not ψ)
| orl : Subformula φ ψl → Subformula φ (.or ψl ψr)
| orr : Subformula φ ψr → Subformula φ (.or ψl ψr)

def Subformula.decidable [DecidableEq V] : DecidableRel (α := Formula V) Subformula
| φ, ψ =>
  if h : φ = ψ then by
    apply isTrue
    apply eq
    assumption
  else by
    cases ψ
    case not ψ' =>
      let _ := Subformula.decidable φ ψ'
      if h : Subformula φ ψ' then
        apply isTrue
        apply Subformula.not
        exact h
      else
        apply isFalse
        intro sub
        cases sub <;> contradiction
    case or ψl ψr =>
      -- WIP: efficiency issue? now i think we'll first recurse into both
      -- disjuncts, when we may only need to check one (i.e. we're avoiding
      -- "lazy or")
      let _ := Subformula.decidable φ ψl
      let _ := Subformula.decidable φ ψr
      if h : Subformula φ ψl ∨ Subformula φ ψr then
        apply isTrue
        cases h with
        | inl hl =>
          apply Subformula.orl
          exact hl
        | inr hr =>
          apply Subformula.orr
          exact hr
      else
        rw [not_or] at h
        have ⟨hl, hr⟩ := h
        apply isFalse
        intro sub
        cases sub <;> contradiction

    repeat
      apply isFalse
      intro sub
      cases sub
      contradiction

instance [DecidableEq V] : DecidableRel (α := Formula V) Subformula := Subformula.decidable

namespace Formula

def valuate (v : V → Bool) : Formula V → Bool
| .bot => false
| .var x => v x
| .not φ => !φ.valuate v
| .or φ ψ => φ.valuate v || ψ.valuate v

def equivalent (φ : Formula V) (ψ : Formula V) : Prop :=
  ∀ v, φ.valuate v = ψ.valuate v

infix:50 " ≣ " => equivalent

def tautology (φ : Formula V) : Prop :=
  ∀ v, φ.valuate v = true

prefix:50 " ⊨ " => tautology

theorem tautology_iff_iff_equivalent : ∀ φ ψ : Formula V, ⊨ .iff φ ψ ↔ φ.equivalent ψ := by
  intro φ ψ
  constructor
  · intro h
    intro v
    have h' := h v
    simp [valuate] at h'
    have ⟨hl, hr⟩ := h'
    if h : φ.valuate v then
      sorry
    else
      sorry
  · intro h
    intro v
    simp [valuate]
    rw [h]
    simp


-- def valuate (v : V → Prop) : Formula V → Prop
-- | .bot => False
-- | .var x => v x
-- | .not φ => ¬φ.valuate v
-- | .or φ ψ => φ.valuate v ∨ ψ.valuate v

-- def valuate.decidable (v : V → Prop) (decideVar : (x : V) → Decidable (v x)) :
--   (φ : Formula V) → Decidable (φ.valuate v)
-- | .bot => by
--   rw [valuate]
--   exact inferInstance
-- | .var x => decideVar x
-- | .not φ => by
--   rw [valuate]
--   let _ := decidable v decideVar φ
--   exact inferInstance
-- | .or φ ψ => by
--   rw [valuate]
--   let _ := decidable v decideVar φ
--   let _ := decidable v decideVar ψ
--   exact inferInstance

end Formula

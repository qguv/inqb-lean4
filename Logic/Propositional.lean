import Mathlib.Data.Vector.Defs
import Mathlib.Data.Vector.Basic
-- import Mathlib.Data.Set.Defs
-- import Mathlib.Data.Finset.Basic

open Mathlib

class Connective (α : Type u) where
  arity : α → Nat

inductive Expr.Ty where
| bool : Ty
| args : Nat → Ty

inductive Expr (V : Type) (C : Type) [inst : Connective C] : Expr.Ty → Type where
| var : V → Expr V C .bool
| conn :
  (c : C) →
  Expr V C (.args (inst.arity c)) →
  Expr V C .bool
| nilArg : Expr V C (.args 0)
| consArg : Expr V C (.bool) → Expr V C (.args n) → Expr V C (.args (n + 1))
deriving Repr

instance instDecidableEqExpr [Connective C] [DecidableEq V] [DecidableEq C] :
  DecidableEq (Expr V C τ)
| φ, ψ => by
  induction φ <;> cases ψ
  case' var.var x y =>
    if h : x = y then
      apply isTrue
      rw [h]
    else _
  case' conn.conn c xs ih d ys =>
    by_cases h : c = d
    subst h
    have : Decidable (xs = ys) := ih ys
    by_cases h : xs = ys
    apply isTrue
    rw [h]
  case' nilArg.nilArg =>
    apply isTrue
    rfl
  case' consArg.consArg a as ih_a ih_as b bs =>
    have : Decidable (a = b) := ih_a b
    have : Decidable (as = bs) := ih_as bs
    by_cases h1 : a = b
    by_cases h2 : as = bs
    apply isTrue
    rw [h1, h2]
  -- TODO: find a way to avoid the duplication between these two `repeat` blocks
  -- (simply slapping a `try` onto the `injection` doesn't seem to do it)
  repeat
    apply isFalse
    intro eq
    injection eq
    contradiction
  repeat
    apply isFalse
    intro eq
    contradiction

abbrev Formula V C [Connective C] := Expr V C .bool
abbrev Args V C n [Connective C] := Expr V C (.args n)

namespace Connective

inductive Standard where
| bot
| top
| not
| and
| or
| implies
| iff
deriving Repr

instance : Connective Standard where
  arity
  | .bot => 0
  | .top => 0
  | .not => 1
  | .and => 2
  | .or => 2
  | .implies => 2
  | .iff => 2

#check Expr.conn Standard.bot .nilArg
#check Expr.conn Standard.and (.consArg (.var "y") (.consArg (.var "x") .nilArg))

end Connective

mutual
  inductive Subformula [inst : Connective C] (φ : Formula V C) : Formula V C → Prop where
  | rfl : Subformula φ φ
  | conn :
    {args : _} →
    Subformula.OfArgs (n := inst.arity c) φ args →
    Subformula φ (Expr.conn c args)

  inductive Subformula.OfArgs [inst : Connective C] (φ : Formula V C) : Args V C n → Prop where
  | here : Subformula φ ψ → Subformula.OfArgs φ (.consArg ψ ψs)
  | there : Subformula.OfArgs φ ψs → Subformula.OfArgs φ (.consArg ψ ψs)
end

mutual
  instance instDecidableRelSubformula [Connective C] [DecidableEq V] [DecidableEq C] :
    DecidableRel (α := Formula V C) Subformula
  | φ, ψ => by
    if h : φ = ψ then
      apply isTrue
      rw [h]
      exact .rfl
    else
      cases ψ with
      | var x => sorry
      | conn c args =>
          if s : Subformula.OfArgs φ args then
            apply isTrue
            exact .conn s
          else
            apply isFalse
            intro s
            cases s <;> contradiction

  instance instDecidableSubformulaOfArgs [Connective C] [DecidableEq V] [DecidableEq C] (φ : Formula V C) :
    (args : Expr V C (.args n)) → Decidable (Subformula.OfArgs φ args)
  | args => by
    cases args with
    | nilArg =>
        apply isFalse
        intro s
        cases s
    | consArg ψ ψs =>
        if h : Subformula φ ψ then
          apply isTrue
          -- exact .here (ψs := ψs) h
          sorry
        else
          if h' : Subformula.OfArgs φ ψs then
            apply isTrue
            -- exact .there h'
            sorry
          else
            apply isFalse
            intro s
            cases s
            repeat sorry
end

#check Expr.rec

mutual
  def Formula.fold [inst : Connective C] (var : V → α) (conn : (c : C) → Vector α (inst.arity c) → α) :
    Formula V C → α
  | .var v => var v
  | .conn c args => conn c (Args.fold var conn args)

  def Args.fold [inst : Connective C] (var : V → α) (conn : (c : C) → Vector α (inst.arity c) → α) :
    Args V C n → Vector α n
  | .nilArg => .nil
  | .consArg φ φs => .cons (Formula.fold var conn φ) (Args.fold var conn φs)
end

namespace Connective

def Standard.valuate : (c : Standard) → Vector Prop (Connective.arity c) → Prop
| .bot, .nil => ⊥
| .top, .nil => ⊤
| .not, p ::ᵥ .nil => ¬p
| .and, p ::ᵥ q ::ᵥ .nil => p ∧ q
| .or, p ::ᵥ q ::ᵥ .nil => p ∨ q
| .implies, p ::ᵥ q ::ᵥ .nil => p → q
| .iff, p ::ᵥ q ::ᵥ .nil => p ↔ q

def Formula.valuate : (V → Prop) → Formula V Standard → Prop
| v, φ => φ.fold v Standard.valuate

#eval
  fun x y =>
  Formula.valuate
    ( fun v => match v with
      | "x" => x
      | "y" => y
      | _ => False
    )
    (.conn .and (.consArg (.var "y") (.consArg (.var "x") .nilArg)))

end Connective

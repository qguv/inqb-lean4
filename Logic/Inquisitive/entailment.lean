import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation
import Logic.Inquisitive.types

namespace Inquisitive

variable {W : Type}
variable (p q : Proposition W)

def Proposition.entails := p.truthSet ⊆ q.truthSet
def Proposition.info := ⋃₀ p.truthSet
def Proposition.trueIn (w : W) := w ∈ p.info
def Proposition.isInformative := p.info ≠ Set.univ
def Proposition.isInquisitive := p.info ∉ p.truthSet
def Proposition.isTautology := Set.univ ∈ p.truthSet
def Proposition.alt := { s ∈ p.truthSet | ¬(∃t ∈ p.truthSet, s ⊂ t) }

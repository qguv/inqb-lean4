import Lean

import Logic.Inquisitive.types
import Logic.Inquisitive.ops
import Logic.Inquisitive.projections

namespace Inquisitive

macro p:ident "*" : term => do
  `(Proposition.absolutePseudoComplement $p)

macro p:ident " ∩ᵢ " q:ident : term => do
  `(Proposition.meet $p $q)

macro p:ident " ⋃ᵢ " q:ident : term => do
  `(Proposition.join $p $q)

macro "?" p:ident : term => do
  `(Proposition.decisionSet $p)

macro "!" p:ident : term => do
  `(Proposition.bang $p)

macro "⁉" p:ident : term => do
  `(Proposition.bang (Proposition.decisionSet $p))

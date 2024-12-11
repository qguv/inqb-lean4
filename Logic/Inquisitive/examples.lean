import Logic.Inquisitive.types
import Logic.SetLemmas

namespace Inquisitive

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
  downwardClosed := SetLemmas.powerset_downward_closed {p, pq}

import Logic.Inquisitive.types
import Logic.Inquisitive.lemmas

namespace Inquisitive

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
  downwardClosed := lemmas.powerset_downward_closed {p, pq}

#print foo.proof_2

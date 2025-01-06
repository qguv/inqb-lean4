#import "inquisitive-semantics-20241129.typ": *

#let course = [Logic & Conversation]
#let course_period = [Fall 2024]
#let university = [Universiteit van Amsterdam]
#let title = [Formalizing InqB in Lean 4]
#let author = (
  markup: [Quint #smallcaps[Guvernator]],
  string: "Quint Guvernator",
)

/////////////////////////////////////////
// settings
/////////////////////////////////////////
#set text(lang: "en", number-type: "old-style", discretionary-ligatures: true, size: 12pt)
#set par(justify: true, leading: 0.8em)
#set document(title: course + ": " + title, author: author.string)
#set page(footer: context {
  set align(center)
  
  counter(page).display(
    "— 1 —",
    both: false,
  )
})

/*
#set page(footer: context [
  #line(length: 100%, stroke: 0.1pt)
    #grid(
      columns: (1fr, auto, 1fr),
      align: (left, center, right),
      title,
      counter(page).display(
        "— 1 —",
        both: false,
      ),
      author.markup,
    )
])
*/

// bigger h1
#show heading.where(level: 1): set text(22pt)

// number headings
#set heading(numbering: "1.")

// hide numbers inline for headers below h3 (but keep them in the outline)
//#show heading: it => if it.level > 2 { [#block(it.body)] } else { it }

// ignore h4, h5 altogether in outline
#show heading.where(level: 4): set heading(outlined: false, numbering: none)
#show heading.where(level: 5): set heading(outlined: false, numbering: none)

// flowery italics
#show emph: set text(historical-ligatures: true)

// give square brackets more space
#show math.lr: it => {
  let c = it.body.children
  if (
    c.len() >= 3
    and c.at(0) == [\[]
    and c.at(-1) == [\]]
    and c.at(1) != math.med
    and c.at(-2) != math.med
  ) {
    let inner = it.body.children.slice(1, -1)
    $med lr(size: #110%,
      \[ med #inner.join("") med \]
    ) med$
  } else {
    it
  }
}

// list styles
#set list(marker: sym.quote.angle.r.single)
#set enum(indent: 1em, numbering: "a.")

// lean4 syntax highlighting
#set raw(syntaxes: "lean4.sublime-syntax")

// smaller text in code
#show raw.where(block: true): set text(8pt)

// clearer links
#show link: underline
#show link: set text(blue)

#let see(label, ..content) = [
  #set par(justify: false)
  _See:
  #if content.pos().len() > 0 { content.pos().first() }
  _
  #if content.pos().len() > 0 { "at" }
  #ref(label)
]

#let repofile(path) = box(link("https://github.com/qguv/inqb-lean4/blob/termpaper/" + path)[#raw(path)])

#let see_repofile(..paths) = [
  #see(<repo>, for path in paths.pos() [#repofile(path), ])
]

// add some extra spacing around figures
//#show figure: it => box(inset: .5em, it)

// smaller text in code blocks
#show figure.where(kind: raw): set text(10pt)

// draw vertical line next to code blocks
#show raw.where(block: true): it => box(stroke: (left: 1pt), inset: 1em, it)

// add line numbers to code blocks
#show raw.where(block: true): it => {
  show raw.line: line => {
    box(width: 2em, text(fill: gray)[#line.number])
    line.body
  }
  it
}

// refer to code figures as "snippets"
#show figure.where(kind: raw): set figure(supplement: "Snippet")


/////////////////////////////////////////
// globals
/////////////////////////////////////////

#let bot = math.class("normal", sym.bot)
#let inq = math.class("unary", "?")
#let bang = math.class("unary", "!")
#let comp = math.class("unary", "*")
#let yes = text(green, sym.checkmark)
#let no = text(red, sym.crossmark)
#let TODO = box(stroke: red, height: .6em, inset: (x: .23em))[#align(horizon)[#text(size: 6pt)[??]]]
#let InqB = [*InqB*]
#let ind(..opts) = box(
  inset: (left: 1em),
  stroke: (left: 1pt),
  ..opts,
)
#let pink = rgb(220, 100, 255)
#let nice-gray = rgb(100, 100, 100)
#let entails = math.tack.double.r
#let sem(phi) = $lr(bracket.double #phi bracket.double.r)$
#let powerset = "𝒫"
#let fullscreen-pic(body) = align(center, body)

/////////////////////////////////////////
// title
/////////////////////////////////////////

#grid(
  columns: (1fr, 1fr),
  align: (left+bottom, right+horizon),
  [
    #set par(spacing: .5em)
    
    #text(21pt, course)
    
    #text(17pt, course_period)
  ],
  image("uva.svg"),
)
#align(center, line(length: 100%))

#align(center, box(width: 80%)[

    // title
    #box(inset: (y: 35pt))[
      #set par(spacing: .5em)
      #text(24pt, title)
  
      #text(15pt, author.markup)
    ]

    #set align(left)
    #set text(10pt)
    
    ==== Abstract
    The basic Inquisitive Logic (#InqB) as presented in the Inquisitive Semantics book @book is a logic that can be used to model declarative and inquisitive utterances in natural language.
    Lean 4 @lean is an automated theorem prover that can verify and help write mathematical proofs.
    This project @repo aims to formalize #InqB in Lean,
    producing a library that future logicians can use to compute and verify facts about the logic,
    as well as several Lean implementations of theorems from @book,
    allowing Lean's runtime to check their correctness.

    #show heading: set block(above: 2em)
    
    ==== Acknowledgements
    Special thanks to Malvin Gattinger and Daan Rijks for their assistance with Lean.

    ==== Contents
    #outline(title: none)
])
#pagebreak()

/////////////////////////////////////////
// body
/////////////////////////////////////////

= Background

== #InqB
#see(<book>)

#InqB is the logic of _inquisitive propositions_ (hereafter referred to simply as _propositions_) which can be used to represent declarative or inquisitive sentences in natural language.
The logic defines _information states_, sets of possible worlds, as well as _propositions_, sets of information states which are downward closed, non-empty, and closed under the binary operations
_meet_ ($p sect q$),
_join_ ($p union q$),
and _relative pseudo-complement_ ($p -> q$);
as well as the unary operations
_absolute pseudo-complement_ ($p comp$),
_issue-cancellation_ ($#bang p$),
and _info-cancellation_ ($#inq p$).
There are also other operations defined on propositions without these closure properties, such as
$"info"(p)$
and
$"alt"(p)$.

#InqB also defines conditions under which a proposition is _true_ in a particular world, as well as the conditions under which an information state _supports_ a proposition.

Finally, #InqB defines the conditions under which a proposition _entails_ another ($p #entails q$).
This relationship describes which responses serve as suitable answers to a particular question,
while simultaneously specifying which declarative proposition are deducible from others.

Contexts are also a key feature of #InqB, but are out of scope for this project, as are extensions of #InqB to first-order logic.

== Lean 4
#see(<lean>)

Lean is an interactive theorem prover and functional programming language. When a user writes a proof in the Lean language, Lean's runtime can check the proof's correctness. Additionally, Lean can assist in writing proofs, keeping track of the current proof goal as well as any in-scope assumptions. Lean is based on the Calculus of Constructions, a particular version of dependent type theory; as a consequence, any _constructive_ Lean proof can be executed, and the resulting structure can be inspected directly.

The axioms, structures, operations, and theorems available to be used in proofs are provided by `mathlib` @mathlib though, as this project demonstrates, users can also define custom libraries to formalize concepts from fields outside of axiomatic mathematics.

Users can represent natural deduction proofs in a tree structure, which Lean's runtime can check for correctness.
However, Lean also enables users to write proofs interactively using _tactics_:
a sequence of transformations to the current proof goal or in-scope assumptions,
guiding the two closer toward each other until they meet.
This style of proof is closer to natural language formulations of mathematical proofs
and enables the use of semi-automated solvers, such as
resolution solvers,
tableau solvers,
SMT solvers,
CAS systems,
and more.
Such solvers can assist the user through an otherwise tricky proof, as well as help bring tools from one field to another, unifying disparate fields and helping solve previously intractable problems.

Tactic proofs are fundamentally _interactive_ and can be stepped through.
At each step,
Lean shows the _proof state_:
a list of in-scope assumptions followed by the current proposition _goal_ that is being proved.
Where relevant, the proof state is included when describing example proofs in the sections below.

All (non-trivial) proofs in this project are implemented as tactic proofs.
Note, however, that _this_ project avoids using any automated solvers to prove basic facts about #InqB,
as such proofs would not be very instructive and would make this paper quite opaque.
I chose to avoid using automatic tactics such as `simp` and `aesop`,
preferring more manual tactics with straightforward effects, such as `simp only` and `rw`.
The promise of automated solving, at the cost of more opaque proofs, is left for future users of this project to explore and potentially benefit from.

/*
== Tactics: _interactive_ theorem proving

- Start with a set of *hypotheses* and a *goal*

- *Your task:* make these two meet
  - Lean keeps track of your *progress*

- Rewrite the hypotheses or the goal by applying *tactics*
  - see how the hypotheses and goal are affected
  - split goals into *sub-goals*
  - reason in *cases*
  - delegate sub-goals to domain-specific *solvers*

#fullscreen-pic(image("tactics1.png"))
#fullscreen-pic(image("tactics2.png"))
*/

= Objective

This project establishes a computational representation of the structures, operations, and axioms of #InqB in Lean.

By proving theorems from the book @book,
some of which are missing
@book[fact 2.14, p. 22]
or left as exercises to the reader
@book[fact 3.14/exercise 3.6, p. 55/57].
this project helps to complete the mathematical foundations of #InqB.

Additionally, having a Lean formalization permits logicians to use automated tactics from other fields to solve problems or write proofs about #InqB propositions.

Also, and perhaps more importantly, a computational formalization for #InqB can assist future logicians wishing to extend #InqB to account for semantic phenomena that it is not yet equipped to handle.
As explained in the final sentence of the book:

#ind[
  #quote[
    We do not see the basic framework presented here as a final product but much rather as a point of departure.
  ]
  @book[p. 196]
]

If #InqB is meant as a starting point, then those wishing to extend it will need to ensure that their new logical framework does not break existing properties of the logic, or otherwise provide replacement definitions for the basic operations. Logicians can use the Lean definitions of propositions, operations, and basic theorems to check whether existing proofs are still valid, and can use Lean's interactive features to assist in finding solutions if this is not the case.

Finally, a Lean implementation of #InqB enables users to compute concrete expressions automatically. While simple diagrams with four possible worlds are simple enough to compute by hand, this process becomes prone to error when applied to more complex expressions involving several propositions and multiple operators.

== About this paper

This paper is an attempt to walk through a selection of the Lean code that makes up the definitions,
as well as explain instances where the _representation_ of definitions and proofs related to #InqB differ from those in the book.
I have tried to capture the stepwise nature of the tactic proofs discussed below,
showing the proof state before and after important steps,
but please note that the ink-on-paper medium is limited in this respect.
For the _best_ experience,
I would encourage the reader to pull down the repository in a Lean environment and follow along.
This allows the proof state to be inspected at _any_ step of a tactic proof.

= Implementation

== Proposition structure

#see_repofile("Logic/Inquisitive/types.lean")

An inquisitive proposition is modelled as:
a set of sets of possible worlds,
a proof that the above is downward closed,
and
a proof that the above contains the empty set.
The definition of a `Proposition` in Lean is included below as @prop.

#figure(caption: [Lean definition of a proposition])[```lean4
variable (W : Type)
structure Proposition : Type where
  truthSet : Set (Set W)
  downwardClosed : ∀s ∈ truthSet, 𝒫 s ⊆ truthSet
  containsEmpty : ∅ ∈ truthSet
```] <prop>

Two parts of this definition deserve special attention: the world type `W` and the stipulation that every proposition contains the empty set.

==== Worlds

`Proposition` is defined inductively on a world type `W`, which specifies the type that worlds of a particular proposition will be.
Because this definition does not impose any constraints on what type `W` must be,
users can represent worlds in a particular proposition using any type they like.
As a consequence,
an individual instance of a proposition will not be of type `Proposition` but of type `Proposition W` for some concrete type `W`, i.e. `Proposition Nat`.

==== Non-emptiness

The definition of a proposition in @book merely stipulates that propositions are non-empty,
whereas the Lean definition stipulates that for each proposition $p$,
$emptyset in p$ _in particular_.
The adjusted stipulation makes some proofs easier to write,
and the two stipulations are equivalent because of downward closure.
Getting from the latter to the former is trivial:
$emptyset in p$ directly implies that $p != emptyset$.
For the other direction
(that non-emptiness and downward closure together imply `containsEmpty`),
consider an arbitrary proposition $p$.
Because $p$ is non-empty,
there exists some $x in p$.
Then by downward closure,
$powerset x subset.eq p$.
As $emptyset$ is a member of every powerset,
we know $emptyset in p$.

== Instantiating a proposition <inst>

#see_repofile(
  "Logic/Inquisitive/examples.lean",
  "Logic/Inquisitive/lemmas.lean",
  "Logic/SetLemmas.lean",
)

To reason about a particular proposition, a user must first instantiate it by:

- specifying the set `W` of all possible worlds (which is of particular importance when computing the absolute complement of the proposition);
- designating which sets of these worlds are contained in the proposition's `truthSet`;
- proving that the `truthSet` is downward closed; and
- proving that the `truthSet` contains the empty set.

For trivial examples, this can be quite tedious, so the library contains two simple lemmas to make this easier: `powerset_downward_closed` and `emptyset_in_powerset`. This allows users to create propositions in the following way:

- specify a world type `W`;
- specify the set of top-level alternatives in the truth set, and create the truth set from the union of their powersets;
- use the `powerset_downward_closed` lemma to show downward closure; and
- use the `emptyset_in_powerset` lemma to show that `truthSet` contains the empty set.

== Operations

#see_repofile("Logic/Inquisitive/ops.lean")

Each algebraic operation is defined simply by instantiating the proposition that results from applying the operation on its operand(s). This means that our operator definitions, like any other instantiation, consist of the same four steps described above.

As @book does not specify the results of a binary operation between propositions spanning over different sets of worlds,
the library permits binary operations only between propositions over the same set of worlds.
The resulting proposition will span over the same set of worlds and will therefore have the same type as its operands.

The truth set resulting from each operation is specified directly in @book. This library uses these definitions verbatim wherever possible, as Lean is expressive enough to understand the set theoretic symbols used for these definitions.

So for each proposition, the main task is to provide proofs that, if the operands are downward closed and contain the empty set, the resulting proposition will also be downward closed and contain the empty set.

This library defines tactic proofs for the closure properties of all algebraic operations:

+ meet ($p sect q$),
+ join ($p union q$),
+ absolute pseudo-compliment ($p comp$), and
+ relative pseudo-compliment ($p -> q$);

as well as the projection operations:

#set enum(start: 5)
+ the information-cancelling operator ($inq p$), and 
+ the issue-cancelling operator ($bang p$).
#set enum(start: 1)

=== Example: relative pseudo-complement

As an example, consider the definition of relative pseudo-complement, included in three snippets below.

==== `truthSet`

For a set of possible worlds $s$ to be in the resulting proposition,
all its subsets $t subset.eq s$
such that $t in p$,
it must also be true that $t in q$.
Lean's syntax allows us to use the definition from @book almost verbatim.

#figure(caption: [Lean definition of the `truthSet` of the relative pseudo-complement of two propositions])[```lean4
variable {W: Type}
variable (p q : Proposition W)
def Proposition.relativePseudoComplement : Proposition W where
  truthSet := {s | ∀ t ⊆ s, t ∈ p.truthSet → t ∈ q.truthSet}
```] <rpcts>

Note, however, that the Lean definition of a `Proposition` distinguishes between the object itself and its `truthSet`,
while @book does not.
This difference is a consequence of how structures are defined, has no deep meaning, and can be ignored as an implementation detail.

==== `containsEmpty`

This proof needs to show that, given that the operands each contain the empty set, the resulting proposition will also contain the empty set.

#figure(caption: [Lean proof that the relative pseudo-complement of two propositions contains the empty set])[```lean4
variable {W: Type}
variable (p q : Proposition W)
def Proposition.relativePseudoComplement : Proposition W where
  containsEmpty := by
    intro
    intro b
    intro
    rw [Set.subset_empty_iff] at b
    rw [b]
    exact q.containsEmpty
```] <rpcce>

Before any tactics are applied, the proof that the resulting proposition contains the empty set has the state:

```lean4
W : Type
p q : Proposition W
⊢ ∅ ∈ {s | ∀ t ⊆ s, t ∈ p.truthSet → t ∈ q.truthSet}
```

where the final line shows the current _goal_
and the other lines show _in-scope assumptions._
From the definition of a `Proposition`,
we know that the propositions $p$ and $q$ from the assumption on line 2 include proofs that they are downward closed and contain the empty set,
so these proofs are _also_ assumptions which can be used in the proof.

The proof begins by applying the `intro` tactic repeatedly, breaking down the goal by adding assumptions about arbitrary objects into the current scope in the style of a "without loss of generality" proof. After these steps, the proof state is as follows:

```lean4
W : Type
p q : Proposition W
t✝ : Set W
b : t✝ ⊆ ∅
a✝ : t✝ ∈ p.truthSet
⊢ t✝ ∈ q.truthSet
```

The assumption `a✝` now shows a set of worlds `t✝` in scope 
#footnote[
  The strange name `t✝` is chosen automatically by the compiler.
  If a name is provided as an argument to the `intro` tactic,
  the compiler will use this to name the newly created assumption;
  otherwise, it will choose an arbitrary name and add the `✝` suffix.
  This particular assumption is not named because it is never used in the proof;
  but this does not mean that this `intro` application can be skipped!
  It is the _other_ consequence of `intro`,
  namely, that the goal is simplified,
  which the proof depends on.
]
which we know, by assumption `b`, is a subset of the empty set.

The lemma `Set.subset_empty_iff` is then used to rewrite assumption `b`.
The lemma is of the form
$s subset.eq emptyset <==> s = emptyset$,
so the assumption `b` is transformed into a proof that $#`t✝` = emptyset$.

Next, in line 9, the _goal_
#footnote[
  When the `rw` tactic is used without a target (i.e. missing an `at` directive),
  it is the proof's _goal_ that is rewritten.
]
is rewritten using the equivalence in assumption `b`. The resulting goal is `∅ ∈ q.truthSet`.

Note that this goal is encompassed by the original assumption:
that the empty set is a member of each proposition.
The proof therefore concludes on line 10 by using the proof that `q` contains the empty set.

==== `downwardClosed`

The proof of downward closure must start with the assumption that both operands are downward closed
and conclude that the result is also downward closed.

#figure(caption: [Lean proof that the relative pseudo-complement of two propositions is downward closed])[```lean4
variable {W: Type}
variable (p q : Proposition W)
def Proposition.relativePseudoComplement : Proposition W where
  downwardClosed := by
    intro
    intro h1
    rw [Set.mem_setOf] at h1
    intro
    intro h2
    rw [Set.mem_setOf]
    intro t
    intro h3
    rw [Set.mem_powerset_iff] at h2
    have h4 := SetLemmas.subset_trans h3 h2
    exact h1 t h4
```] <rpcdc>

The initial proof state has a particularly messy goal
because the goal contains the definition of relative pseudo-complement twice:

```lean4
W : Type
p q : Proposition W
⊢ ∀ s ∈ {s | ∀ t ⊆ s, t ∈ p.truthSet → t ∈ q.truthSet}, 𝒫 s ⊆ {s | ∀ t ⊆ s, t ∈ p.truthSet → t ∈ q.truthSet}
```

After a two applications of the `intro` tactic, the state becomes somewhat more manageable:

```lean4
W : Type
p q : Proposition W
s✝ : Set W
h1 : s✝ ∈ {s | ∀ t ⊆ s, t ∈ p.truthSet → t ∈ q.truthSet}
⊢ 𝒫 s✝ ⊆ {s | ∀ t ⊆ s, t ∈ p.truthSet → t ∈ q.truthSet}
```

The proof simplifies the definitions of both `h1` and (after a few more `intro` applications) the goal by collapsing the definition of membership of a constructed set, namely that a decision function applied to the member gives a positive result:
$
a ∈ {x | p(x)} <==> p(a)
$
In the case of `h1`, the assumption is simplified to `∀ t ⊆ s✝, t ∈ p.truthSet → t ∈ q.truthSet`.

After several steps of introduction and simplification (immediately after line 12 in @rpcdc), the goal is much simpler, and the various assumptions that can be used as evidence for the goal are much compacter:

```lean4
W : Type
p q : Proposition W
s✝ : Set W
h1 : ∀ t ⊆ s✝, t ∈ p.truthSet → t ∈ q.truthSet
a✝ : Set W
h2 : a✝ ∈ 𝒫 s✝
t : Set W
h3 : t ⊆ a✝
⊢ t ∈ p.truthSet → t ∈ q.truthSet
```

It now suffices to show that, if $t in p$, then $t in q$. This can be proved from a chain of  subset relations: `h3` and `h2` show that $t subset.eq #`a✝` subset.eq #`s✝`$. This satisfies the condition on the universal quantifier in `h1`, so the statement under the quantifier is what needs to be shown.

In tactic form, this is accomplished in the following steps:
- First, line 13 transforms `h2` into a subset definition.
- Then, line 14 uses the transitive property of subset inclusion to combine `h3` and `h2` into a new assumption `h4` showing that $t subset.eq #`s✝`$.
- Finally, the last line uses this new assumption to satisfy the universal quantifier in `h1`, producing a proof that $t in p -> t in q$.

#pagebreak()
= Book proofs

#see_repofile("Logic/Inquisitive/bookproofs.lean")

To demonstrate the formalization in action,
this project also includes a few proofs from @book implemented in Lean.
Each of these proofs is discussed briefly below.
Additionally, the last of these proofs is reproduced in detail,
along with a walk-through of the implementation.

== Truth and support
_See:_ @book[fact 2.14, p. 22]

A proof of the following fact:

$
forall w in W : p "true in" w <==> p "supported by" {w}
$

is absent from the book,
though as seen in the Lean implementation of the proof,
it is by no means trivial.
In fact, other proofs refer to and depend on this fact.
@book[fact 2.19, p. 25]
A Lean proof is provided in the file linked above.

== Alternative characterizations of non-inquisitive propositions
_See:_ @book[fact 2.19, p. 25]

For any proposition P, each of the statements below are equivalent:

#set enum(numbering: "(1)")
+ $p "is non-inquisitive"$
+ $p = 𝒫("info"(p))$
+ $p "has a greatest element"$
+ $p "is supported by" s <--> p "is true in all worlds" w "in" s$

The long and interesting proof of this fact exercises much of Lean's available tactic machinery.
The proof can be found at the file linked above.

== Division
_See:_ @book[fact 3.14/exercise 3.6, p. 55/57]

A key feature of #InqB is that propositions are composed of declarative and inquisitive content:

$
P = bang P sect inq P
$

The Lean proof of this fact is available at the file linked above, but as it is an appropriate size and complexity, it is also reproduced and annotated in detail below.

=== Example: proof that $p = bang p sect inq q$

#figure(caption: [Lean proof of fact 3.14/exercise 3.6])[```lean4
theorem fact_3_14 : p = p.bang.meet p.decisionSet := by

  -- from meet to intersection of truthsets
  unfold Proposition.meet
  apply lemmas.eq_of_truthSet_eq
  simp only

  -- ?p → p ∪ p*
  unfold Proposition.decisionSet
  simp only

  -- distribute ∩ across ∪
  rw [Set.inter_union_distrib_left]

  -- split equality proof into biconditional
  ext x
  constructor

  -- p -> !p ∩ ?p
  case a.h.mp =>
    intro s
    apply Or.inl
    apply And.intro
    case left =>
      unfold Proposition.bang
      simp only
      exact Set.subset_sUnion_of_mem s
    case right =>
      exact s

  -- !p ∩ ?p -> p
  case a.h.mpr =>
    intro s
    cases s with
    | inl h => exact h.right
    | inr h =>
      obtain ⟨info, comp⟩ := h
      unfold Proposition.bang at info
      simp only at info
      rw [Set.mem_powerset_iff] at info
      unfold Proposition.absolutePseudoComplement at comp
      rw [Set.mem_powerset_iff] at comp
      have h := p.containsEmpty
      have h2 := SetLemmas.empty_of_subset_of_compl x info comp
      subst x
      exact h
```]

Note that the expression `p.bang.meet p.decisionSet` above is equivalent to $bang p sect inq p$ but uses method call syntax to denote the meet of the propositions `p.bang` ($bang p$) and `p.decisionSet` ($inq p$).

Before applying any tactics, the proof state is as follows:

```lean4
W : Type
p : Proposition W
⊢ p = p.bang.meet p.decisionSet
```

Once again, due to the closure properties of $!p$ and $?p$, the proofs that these are downward closed and contain the empty set are in scope and can be used in this proof.

The proof starts by applying the definition of _meet_.
Next, a lemma is used to simplify the goal.
#footnote[
  This lemma and the `simp only` line below it are needed because,
  in this context,
  Lean cannot see that propositions are equal iff their truth sets are equal.
  However, Lean _does_ treat all proofs of the same proposition as equivalent,
  so I am not sure why Lean cannot infer the equivalence conditions for the proposition structure here.
]
The proof state now incorporates the definition of _meet_ in the goal:

```lean4
W : Type
p : Proposition W
⊢ p.truthSet = p.bang.truthSet ∩ p.decisionSet.truthSet
```

The next tactics (lines 9--10) modify the goal again using the fact that $inq p <==> p union p comp$. The state now includes the expanded goal:

```lean4
W : Type
p : Proposition W
⊢ p.truthSet = p.bang.truthSet ∩ (p.truthSet ∪ p.absolutePseudoComplement.truthSet)
```

Next, a set theory property is used to distribute the intersection in the goal across the adjacent union, modifying the state once again:

```lean4
W : Type
p : Proposition W
⊢ p.truthSet = p.bang.truthSet ∩ p.truthSet ∪ p.bang.truthSet ∩ p.absolutePseudoComplement.truthSet
```

The equality can now be split into a biconditional by lines 16--17. Each case is now handled separately.

==== $(==>)$

In the left-to-right case, the proof state begins after line 20 as follows:

```lean4
W : Type
p : Proposition W
x : Set W
⊢ x ∈ p.truthSet → x ∈ p.bang.truthSet ∩ p.truthSet ∪ p.bang.truthSet ∩ p.absolutePseudoComplement.truthSet
```

First, `intro s` is used to pull the antecedent out of the goal and add it as an assumption `s`, leaving the consequent behind as the only goal.

Next, because set union is implemented as logical or, the natural deduction definition of _left-hand or introduction_ (called `Or.inl` in Lean) can be applied (in reverse) to the goal to eliminate the second operand of the set union. The goal is now to prove that $x$ is a member of the left operand to the union, as seen in the proof state after line 22:

```lean4
W : Type
p : Proposition W
x : Set W
s : x ∈ p.truthSet
⊢ x ∈ p.bang.truthSet ∩ p.truthSet
```

After this, a similar strategy is used to split the goal into two sub-goals using the natural deduction definition of _and introduction_; to prove that $x$ is a member of the set union of $bang p$ and $p$, it suffices to show that $x in bang p$ and that $x in p$. This creates a goal for each conjunct, which once again are handled in cases.

===== Left conjunct

Given that $x in p$, the goal is to prove that $x in bang p$.
The initial proof state after line 24 is as follows:

```lean4
case h.left
W : Type
p : Proposition W
x : Set W
s : x ∈ p.truthSet
⊢ x ∈ p.bang.truthSet
```

The proof uses the definition of $!p$ to rewrite the goal to $x in powerset("info"(p))$.
From this point,
Lean's notion of _definitional equality_ makes it possible to prove the fact directly,
without use of tactics to instantiate definitions manually.
Because _membership_ of $powerset "info"(p)$ is defined as being a _subset_ of $"info"(p)$,
it will suffice to show that $x subset.eq "info"(p)$.
Furthermore,
because the definition of $"info"(p)$ is the union of the information states of $p$,
it will suffice to show that $x subset.eq union.big p$.

To show this, another set property is used: $x in S -> x subset.eq union.big S$. The antecedent matches the in-scope assumption `s`, so modus ponens, which is simply function application in Lean, is used directly in line 27 to produce the goal.

===== Right conjunct

The initial proof state after line 28 is as follows:

```lean4
case h.right
W : Type
p : Proposition W
x : Set W
s : x ∈ p.truthSet
⊢ x ∈ p.truthSet
```

Note that one of the assumptions, `s`, is precisely the goal.
Proving this goal is as simple as pointing to the assumption `s` using the tactic `exact s`.

==== $(<==)$

For the other direction, once again the antecedent is separated from the goal as a new assumption `s`. After this trivial step, the proof state after line 33 is as follows:

```lean4
W : Type
p : Proposition W
x : Set W
s : x ∈ p.bang.truthSet ∩ p.truthSet ∪ p.bang.truthSet ∩ p.absolutePseudoComplement.truthSet
⊢ x ∈ p.truthSet
```

The proof continues by reasoning in cases for each operand of the union in assumption `s`.

===== Left disjunct

For this case, suppose that $x in bang p sect p$, and call this assumption `h`.
The assumption `s` is no longer available, and the goal remains the same: prove that $x in p$.
The proof state after the arrow in line 35 begins as follows:

```lean4
W : Type
p : Proposition W
x : Set W
h : x ∈ p.bang.truthSet ∩ p.truthSet
⊢ x ∈ p.truthSet
```

As set intersection is implemented as conjunction in Lean,
there are also in-scope assumptions `h.left` ($x in bang p$) and `h.right` ($x in p$).
The latter of these matches the goal exactly,
so the tactic `exact h.right` is used to close this part of the proof.

===== Right disjunct

For this case, suppose that $x in bang p sect p comp$ and call this assumption `h`.
The assumption `s` is, once again, no longer available,
and the goal has not changed.
The proof state after line 36 is as follows:

```lean4
W : Type
p : Proposition W
x : Set W
h : x ∈ p.bang.truthSet ∩ p.absolutePseudoComplement.truthSet
⊢ x ∈ p.truthSet
```

The proof begins at line 37 by separating the two conjuncts corresponding to the operands of the intersection in assumption `h`, which takes `h` out of scope and introduces new assumptions `info` and `comp`.

The next three lines rewrite the assumption `info` using the definitions of $bang p$
and the fact that
membership in $powerset "info"(p)$ is equivalent to being a subset of $"info"(p)$,
giving the following proof state after line 40:

```lean4
W : Type
p : Proposition W
x : Set W
info : x ⊆ p.info
comp : x ∈ p.absolutePseudoComplement.truthSet
⊢ x ∈ p.truthSet
```

Next, the definition of absolute pseudo-complement is used to rewrite the assumption `comp`, and the same set property is used, giving the following proof state after line 42:

```lean4
W : Type
p : Proposition W
x : Set W
info : x ⊆ p.info
comp : x ⊆ (⋃₀ p.truthSet)ᶜ
⊢ x ∈ p.truthSet
```

The next step involves a set property that is not directly defined in Lean, but that is proved in #repofile("Logic/SetLemmas.lean"):
$
a subset.eq A and a subset.eq A^c ==> a = ∅
$

Because $"info"(p)$ is defined as $union.big p$, we can instantiate this identity using the two assumptions `info` and `comp`, producing a new assumption `h2` that $x = emptyset$. The state of the proof after line 44 is then:

```lean4
W : Type
p : Proposition W
x : Set W
info : x ⊆ p.info
comp : x ⊆ (⋃₀ p.truthSet)ᶜ
h : ∅ ∈ p.truthSet
h2 : x = ∅
⊢ x ∈ p.truthSet
```

Next, the `subst x` tactic is used. This looks for an in-scope assumption (`h2`) with an equivalence relation between `x` and some other object ($emptyset$), and then replaces each instance of `x` with the object it is equivalent to, removing the equivalence assumption `h2` as well as `x` itself. This has quite an effect on the list of in-scope assumptions, as can be seen in the proof state after line 45:

```lean4
W : Type
p : Proposition W
h : ∅ ∈ p.truthSet
info : ∅ ⊆ p.info
comp : ∅ ⊆ (⋃₀ p.truthSet)ᶜ
⊢ ∅ ∈ p.truthSet
```

Finally, the goal can be cleared by pointing to the matching assumption `h`.
This concludes the right disjunct, closing the right-to-left direction and concluding the proof.

//#fullscreen-pic(image("bookproof.png"))

/*
= Computational examples

#fullscreen-pic(image("instantiate.png"))

In addition to proving facts about #InqB or proposed extensions,
a computational implementation of #InqB enables users to compute the results of operations on concrete propositions.

// compute some world sets, show some lil' guys
*/

= Conclusion

This paper has introduced Lean implementations of propositions and operators in #InqB,
as well as walked through two proofs in detail,
showing how the assumptions and goals change as tactics are applied.

== Future work

The project is open source @repo and patches are welcome.
Some interesting avenues for extension are discussed below:

==== First-order extensions

This project concentrated on the basic operations without consideration for quantifiers. Support for these could be added semantically, and the extent to which this would diverge from Lean's own notion of quantifiers remains to be shown.

==== Syntactic definitions of operators

This project uses semantic definitions for each operation, but computation on specific proposition instances could be made more efficient by providing syntactic rules which could be used to manipulate sentences in #InqB without going through semantics.

==== Custom syntax

Lean allows libraries to define custom syntax,
which allows users to write expressions in Lean that better match the domain they are working with.
For example, perhaps `!p` could be used directly in Lean code instead of `p.bang`.

==== Visualizing propositions

Additionally, Lean allows custom HTML to be sent to the info view for rendering.
For concrete propositions defined in terms of a finite set of possible worlds,
diagrams could be shown to help visualize inputs and results of operations.

==== Simple interface to compute with concrete propositions

Instantiating and computing operations on concrete propositions currently involves creating concrete instances in code.
The shortcut lemmas discussed in @inst above make this somewhat less tedious,
but an even better solution would be not to require users to write code at all.
A simple interface which takes #InqB formulas,
computes the expression,
and visualizes this resulting proposition
could be of practical use,
especially as the number of world grows.
Such a tool could also be used to create visualizations,
for example,
a four-world version of the entailment lattice for three-world propositions found at @book[figure 3.4, p. 50].

== Personal reflection

This project allowed me to gain a deeper understanding of #InqB and how it functions as a logical framework.
It has also allowed me to explore Lean and build experience writing tactic proofs.

#bibliography("refs.yaml", full: true)

#align(bottom+right, scale(3em, w[.:]))
variable (p q r : Prop)

-- commutativity of ∧
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (λ h : p ∧ q ↦ And.intro h.right h.left)
    (λ h : q ∧ p ↦ And.intro h.right h.left)

-- commutativity of ∨
example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (
      λ h : p ∨ q ↦ Or.elim h
        (λ hp : p ↦ Or.inr hp)
        (λ hq : q ↦ Or.inl hq)
    )
    (
      λ h : q ∨ p ↦ Or.elim h
        (λ hq : q ↦ Or.inr hq)
        (λ hp : p ↦ Or.inl hp)
    )

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (
      λ h : (p ∧ q) ∧ r ↦
        have hp : p := h.left.left
        have hq : q := h.left.right
        have hr : r := h.right
        ⟨hp, ⟨hq, hr⟩⟩
    )
    (
      λ h : p ∧ (q ∧ r) ↦
        have hp : p := h.left
        have hq : q := h.right.left
        have hr : r := h.right.right
        ⟨⟨hp, hq⟩, hr⟩
    )

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (
      λ h : (p ∨ q) ∨ r ↦
        Or.elim h
          (
            λ hpq : p ∨ q ↦
              Or.elim hpq
                (λ hp : p ↦ Or.inl hp)
                (λ hq : q ↦ Or.inr $ Or.inl hq)
          )
          (λ hr : r ↦ Or.inr $ Or.inr hr)
    )
    (
      λ h : p ∨ (q ∨ r) ↦
        Or.elim h
          (λ hp : p ↦ Or.inl $ Or.inl hp)
          (
            λ hqr : q ∨ r ↦ Or.elim hqr
              (λ hq : q ↦ Or.inl $ Or.inr hq)
              (λ hr : r ↦ Or.inr hr)
          )
    )

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (
      λ h : p ∧ (q ∨ r) ↦
        have hp : p := h.left
        have hqr : q ∨ r := h.right
        Or.elim hqr
          (λ hq : q ↦ Or.inl ⟨hp, hq⟩)
          (λ hr : r ↦ Or.inr ⟨hp, hr⟩)
    )
    (
      λ h : (p ∧ q) ∨ (p ∧ r) ↦
        Or.elim h
          (
            λ hpq : p ∧ q ↦
              have hp : p := hpq.left
              suffices hq : q from And.intro hp $ Or.inl hq
              show q from hpq.right
          )
          (
            λ hpr : p ∧ r ↦
              have hp : p := hpr.left
              have hr : r := hpr.right
              ⟨hp, Or.inr hr⟩
          )
    )

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (
      λ h : ¬(p ∨ q) ↦
        And.intro
          (λ hp : p ↦ h $ Or.inl hp)
          (λ hq : q ↦ h $ Or.inr hq)
    )
    (
      λ h : ¬p ∧ ¬q ↦
        have hnp : ¬p := h.left
        have hnq : ¬q := h.right
        λ hpq : p ∨ q ↦ Or.elim hpq hnp hnq
    )

example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry

example : ¬(p ∧ ¬p) :=
  λ hpnp : p ∧ ¬p ↦
    absurd hpnp.left hpnp.right

example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry

example : (p → q) → (¬q → ¬p) :=
  λ hpq : p → q ↦
    λ hnq : ¬q ↦
      λ hp : p ↦
        absurd (hpq hp) hnq

module IPL where
  -- Conjunction
  data _∧_ (P : Set) (Q : Set) : Set where
    ∧-intro : P → Q → (P ∧ Q)

  -- elimination rules
  proof₁ : {P Q : Set} → (P ∧ Q) → P
  proof₁ (∧-intro p q) = p

  proof₂ : {P Q : Set} → (P ∧ Q) → Q
  proof₂ (∧-intro p q) = q

  -- bijection
  _⇔_ : (P : Set) → (Q : Set) → Set
  a ⇔ b = (a → b) ∧ (b → a)

  -- Properties
  -- commutative rule
  ∧-comm' : {P Q : Set} → (P ∧ Q) → (Q ∧ P)
  ∧-comm' (∧-intro p q) = ∧-intro q p

  ∧-comm : {P Q : Set} → (P ∧ Q) ⇔ (Q ∧ P)
  ∧-comm = ∧-intro ∧-comm' ∧-comm'

  -- associative rule
  ∧-assoc₁ : { P Q R : Set } → ((P ∧ Q) ∧ R) → (P ∧ (Q ∧ R))
  ∧-assoc₁ (∧-intro (∧-intro p q) r) = ∧-intro p (∧-intro q r)

  ∧-assoc₂ : { P Q R : Set } → (P ∧ (Q ∧ R)) → ((P ∧ Q) ∧ R)
  ∧-assoc₂ (∧-intro p (∧-intro q r)) = ∧-intro (∧-intro p q) r

  ∧-assoc : { P Q R : Set } → ((P ∧ Q) ∧ R) ⇔  (P ∧ (Q ∧ R))
  ∧-assoc = ∧-intro ∧-assoc₁ ∧-assoc₂

  -- Disjuntion
  data _∨_ (P Q : Set) : Set where
    ∨-intro₁ : P → P ∨ Q
    ∨-intro₂ : Q → P ∨ Q

  ∨-elim : {A B C : Set} → (A ∨ B) → (A → C) → (B → C) → C
  ∨-elim (∨-intro₁ a) ac bc = ac a
  ∨-elim (∨-intro₂ b) ac bc = bc b

  -- Properties
  -- commutative rule
  ∨-comm' : {P Q : Set} → (P ∨ Q) → (Q ∨ P)
  ∨-comm' (∨-intro₁ p) = (∨-intro₂ p)
  ∨-comm' (∨-intro₂ q) = (∨-intro₁ q)

  -- associative rule
  -- ∨-assoc: { P Q R : Set } → ((P ∨ Q) ∨ R) ⇔ (P ∨ (Q ∨ R))

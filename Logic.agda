module Logic where

  data _≡_ {A : Set} : A → A → Set where
    relf : {x : A} → x ≡ x

  sym : {A : Set} → (a b : A) → a ≡ b → b ≡ a
  sym a .a relf = relf

  trans : {A : Set} → (a b c : A) → a ≡ b → b ≡ c → a ≡ c
  trans a .a .a relf relf = relf

  cong : {A B : Set} → (f : A → B) → (a b : A) → a ≡ b → f a ≡ f b
  cong f a .a relf = relf

  data _∧_ (A B : Set) : Set where
    _,_ : A → B → A ∧ B

  infixl 6 _∧_

  data _∨_ (A B : Set) : Set where
    inl : A → A ∨ B
    inr : B → A ∨ B

  infixl 5 _∨_

-- Hilbert-style laws
  and1 : {A B : Set} → A ∧ B → A
  and1 (x , x₁) = x

  and2 : {A B : Set} → A ∧ B → B
  and2 (x , x₁) = x₁

  and3 : {A B : Set} → A → B → A ∧ B
  and3 a b = a , b

  or1 : {A B : Set} → A → A ∨ B
  or1 a = inl a

  or2 : {A B : Set} → B → A ∨ B
  or2 b = inr b

  or3 : {A B C : Set} → (A → C) → (B → C) → ((A ∨ B) → C)
  or3 f g (inl x) = f x
  or3 f g (inr x) = g x

  -- top
  data ⊤ : Set where
    tt : ⊤

  -- Bottom the empty set
  data ⊥ : Set where

  falsity : {A : Set} → ⊥ → A
  falsity ()

  --Negation
  ¬ : Set → Set
  ¬ A = A → ⊥

  -- Reductio ad absurdum
  not1 : {A B : Set} → (A → B) → (A → ¬ B) → ¬ A
  not1 f g a = g a (f a)

  not2 : {A B : Set} → A → ¬ A → B
  not2 a na = falsity (na a)

  -- Laws of thought
  postulate LEM : {A : Set} → A ∨ ¬ A
  postulate DNE : {A : Set} → ¬ (¬ A) → A

  -- De Morgan laws
  DeMorgan1 : {P Q : Set} → ¬ (P ∨ Q) → (¬ P) ∧ (¬ Q)
  DeMorgan1 f = and3 (λ p → f (inl p)) (λ q → f (inr q))

  DeMorgan2 : {P Q : Set} → (¬ P) ∧ (¬ Q) → ¬ (P ∨ Q)
  DeMorgan2 (np , nq) (inl x) = np x
  DeMorgan2 (np , nq) (inr x) = nq x

  DeMorgan3 : {P Q : Set} → ¬ (P ∧ Q) → (¬ P) ∨ (¬ Q)
  DeMorgan3 f with LEM
  DeMorgan3 f | inl p = inr (λ q → f (p , q))
  DeMorgan3 f | inr np = inl np

  DeMorgan4 : {P Q : Set} → (¬ P) ∨ (¬ Q) → ¬ (P ∧ Q)
  DeMorgan4 (inl x) (p , q) = x p
  DeMorgan4 (inr x) (p , q) = x q

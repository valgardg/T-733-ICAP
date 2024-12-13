-- Intro to computer-assisted proof

-- Negation, decidable statements

{-# OPTIONS --allow-unsolved-metas #-}

module Logic where


{-
⊤ is entered as \top
-}

data ⊤ : Set where       -- canonical singleton set / canonically true statement
  tt : ⊤

{-
⊥ is entered as \bot
¬ is entered as \neg
-}

data ⊥ : Set where       -- the empty set / canonically false statement


⊥-elim : {P : Set} → ⊥ → P
⊥-elim ()                -- the function from the empty set to any other / falsity implies anything


¬_ : Set → Set           -- negation of a statement 
¬ P = P → ⊥

infix 3 ¬_


data Dec (P : Set) : Set where    -- decidability of a statement
  yes : P → Dec P                -- P is decided if either P itself has a proof or ¬ P has a proof
  no  : ¬ P → Dec P


Decidable : {A B : Set} → (A → B → Set) → Set
Decidable {A} {B} _~_ = (x : A) → (y : B) → Dec (x ~ y)





-- Intro to computer-assisted proof

-- Booleans

{-# OPTIONS --allow-unsolved-metas #-}

module Bool where

open import Logic
open import PropositionalEquality


data Bool : Set where
  false : Bool
  true  : Bool
  -- false and true are the only elements
  -- false and true are distinct


not : Bool → Bool
not false = true
not true = false
   -- Functions out of datatypes are defined by pattern matching


if_then_else_ : {A : Set} → Bool → A → A → A
   -- The first argument, of type Set, is implicit
   -- A is a name for any element in it
if false then _ else y = y
if true  then x else _ = x


infix 0 if_then_else_



not' : Bool → Bool
not' b =  if b then false else true 


{-
≡ is entered as \equiv or \==
-}

not-invol : (b : Bool) → not (not b) ≡ b
not-invol false = refl {_} {false}
not-invol true = refl {_} {true}
  -- The type is a theorem here
  -- The function itself is a proof of it



{-
∧ is entered as \wedge
-}

_∧_ : Bool → Bool → Bool
false ∧ _ = false
true  ∧ b = b

infixr 6 _∧_



{-
ˡ is entered as \^l (and then choosing the correct option among several)
ʳ is entered as \^r (and then choosing the correct option among several)
-}

∧-identityˡ : (b : Bool) → true ∧ b ≡ b
∧-identityˡ _ = refl

∧-identityʳ : (b : Bool) → b ∧ true ≡ b
∧-identityʳ false = refl
∧-identityʳ true = refl

∧-assoc : (b b' b'' : Bool) →  (b ∧ b') ∧ b'' ≡ b ∧ (b' ∧ b'')
∧-assoc false b' b'' = refl
∧-assoc true b' b'' = refl 
{-
∧-comm : (b b' : Bool) → b ∧ b' ≡ b' ∧ b
∧-comm false false = refl
∧-comm false true = refl
∧-comm true false = refl
∧-comm true true = refl
-}

∧-idemp : (b : Bool) → b ∧ b ≡ b
∧-idemp false = refl
∧-idemp true = refl

∧-zeroˡ : (b : Bool) → false ∧ b ≡ false
∧-zeroˡ _ = refl

∧-zeroʳ : (b : Bool) → b ∧ false ≡ false
∧-zeroʳ false = refl
∧-zeroʳ true = refl

∧-comm : (b b' : Bool) → b ∧ b' ≡ b' ∧ b
∧-comm false b' =  sym (∧-zeroʳ b')
∧-comm true b' = sym (∧-identityʳ b')



{-
∨ is entered as \vee
-}

_∨_ : Bool → Bool → Bool
false ∨ b' = b'
true ∨ b' = true 


-- infixr 5 _∨_ _xor_

deMorgan : (b b' : Bool) → not (b ∧ b') ≡ not b ∨ not b'
deMorgan false b' = refl
deMorgan true b' = refl 




⌊_⌋ : {P : Set} → Dec P → Bool
⌊ yes _ ⌋ = true
⌊ no  _ ⌋ = false

T : Bool → Set
T true  = ⊤
T false = ⊥

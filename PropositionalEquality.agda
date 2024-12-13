-- Intro to computer-assisted proof

-- Propositional equality


{-# OPTIONS --allow-unsolved-metas #-}

module PropositionalEquality where

open import Logic

{-
≡ is entered as \equiv or \==
-}


data _≡_ {A : Set} : A → A → Set where      -- x ≡ y is the set of proofs of x equals y
  refl : {x : A} → x ≡ x

infix 4 _≡_

-- x ≡ y contains exactly one element, refl {x}, if x = y (ie x, y are definitionally equal)
-- x ≡ y is empty if x ≠ y

sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
sym refl =  refl 



trans : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl
{-
trans refl q = q        -- this works as well
-}


cong : {A B : Set} → (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
cong _ refl = refl

cong₂ : {A B C : Set} → (_*_ : A → B → C) → {x y : A} → {u v : B} →
      x ≡ y → u ≡ v → x * u ≡ y * v
cong₂ _ refl refl = refl

subst : {A : Set} → (P : A → Set) → {x y : A} → x ≡ y → P x → P y
subst _ refl p = p 

subst₂ : {A B : Set} → (_∼_ : A → B → Set) → {x y : A} → {u v : B} →
      x ≡ y → u ≡ v → x ∼ u → y ∼ v
subst₂ _ refl refl p = p 



data _≡…≡_ {A : Set} : A → A → Set where
  _∎ : (x : A) → x ≡…≡ x 
  _≡⟨_⟩_ : (x : A) → {y z : A} → x ≡ y → y ≡…≡ z → x ≡…≡ z
  _=⟨⟩_ : (x : A) → {z : A} → x ≡…≡ z → x ≡…≡ z

infix 3 _∎
infixr 2 _≡⟨_⟩_
infixr 2 _=⟨⟩_

proof_ : {A : Set} → {x y : A} → x ≡…≡ y → x ≡ y
proof (_ ∎) = refl
-- proof (x ∎) = refl {_} {x}
proof (_ ≡⟨ p ⟩ ps) = trans p (proof ps)
-- proof (x ≡⟨ p ⟩ ps) = trans {_} {x} {_} {_} p (proof ps)
proof (_ =⟨⟩ ps) = proof ps

infix 1 proof_



DecEq : Set → Set
DecEq A = (x y : A) → Dec (x ≡ y)

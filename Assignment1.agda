module Assignment1 where

open import PropositionalEquality
open import Bool
open import List
open import Nat


{-

Assignment 1, ICAP, autumn 2024, deadline Tue 3 Dec 2024 23:59

-}

-- 1.

{-
Prove the stated properties about map and filterᵇ.
-}

map-∘ : {A B C : Set} → (f : A → B) → (g : B → C) → (xs : List A) →
    map (λ x → g (f x)) xs ≡ map g (map f xs) 
map-∘ f g [] = refl
map-∘ f g (x ∷ xs) = cong (_∷_ _) (map-∘ f g xs)


filterᵇ-∧ : {A : Set} → (p q : A → Bool) → (xs : List A) →
    filterᵇ (λ x → p x ∧ q x) xs ≡ filterᵇ q (filterᵇ p xs)
-- filterᵇ-∧ p q xs = {! !}  
filterᵇ-∧ p q [] = refl
filterᵇ-∧ p q (x ∷ xs) = {! !}


-- 2.

{-
Consider the well-known list functions take and drop
for taking resp dropping n first elements of a list
(or all if list has less than n elements).

Prove the stated properties about these functions.
-}

take : {A : Set} → ℕ → List A → List A
take zero xs = []
take (suc m) [] = []
take (suc m) (x ∷ xs) = x ∷ take m xs

drop : {A : Set} → ℕ → List A → List A
drop zero xs = xs
drop (suc m) [] = []
drop (suc m) (x ∷ xs) = drop m xs


++-take-drop : {A : Set} → (m : ℕ) → (xs : List A) →
      take m xs ++ drop m xs ≡ xs
++-take-drop zero xs = refl
++-take-drop (suc m) [] = refl
++-take-drop (suc m) (x ∷ xs) = cong (_∷_ x) (++-take-drop m xs)


drop-+ : {A : Set} → (m n : ℕ) → (xs : List A) →
      drop (m + n) xs ≡ drop n (drop m xs)
drop-+ zero n [] = refl
drop-+ (suc m) zero [] = refl
drop-+ (suc m) (suc n) [] = refl
drop-+ zero n (x ∷ xs) = refl
drop-+ (suc m) zero (x ∷ xs) = drop-+ m zero xs
drop-+ (suc m) (suc n) (x ∷ xs) = drop-+ m (suc n) xs


take-drop-+ : {A : Set} → (m n : ℕ) → (xs : List A) →
      drop m (take (m + n) xs) ≡ take n (drop m xs)
take-drop-+ zero zero [] = refl
take-drop-+ zero zero (x ∷ xs) = refl
take-drop-+ zero (suc n) [] = refl
take-drop-+ zero (suc n) (x ∷ xs) = refl
take-drop-+ (suc m) zero [] = refl
take-drop-+ (suc m) zero (x ∷ xs) = take-drop-+ m zero xs
take-drop-+ (suc m) (suc n) [] = refl
take-drop-+ (suc m) (suc n) (x ∷ xs) = take-drop-+ m (suc n) xs


take-length : {A : Set} → (xs : List A) →
     take (length xs) xs ≡ xs
take-length [] = refl
take-length (x ∷ xs) = cong (_∷_ x) (take-length xs)


take-++ : {A : Set} → (m : ℕ) → (xs ys : List A) →
     take m (xs ++ ys) ≡ take m xs ++ take (m ∸ length xs) ys
take-++ zero [] [] = refl
take-++ zero [] (x ∷ ys) = refl
take-++ zero (x ∷ xs) [] = refl
take-++ zero (x ∷ xs) (x₁ ∷ ys) = refl
take-++ (suc m) [] [] = refl
take-++ (suc m) [] (x ∷ ys) = refl
take-++ (suc m) (x ∷ xs) [] = cong (_∷_ x) (take-++ m xs [])
take-++ (suc m) (x ∷ xs) (x₁ ∷ ys) = cong (_∷_ x) (take-++ m xs (x₁ ∷ ys))


-- 3.

{-
Define the function of maximum of two natural numbers.
Prove that it is associative, idempotent, commutative 
and that addition distributes over maximum from the left.
-}

_max_ : ℕ → ℕ → ℕ
zero max y = y
x max zero = x
(suc x) max (suc y) = suc (x max y)

infixl 5 _max_

max-assoc : (m n p : ℕ) → (m max n) max p ≡ m max (n max p)
max-assoc zero zero zero = refl
max-assoc zero zero (suc p) = refl
max-assoc zero (suc n) zero = refl
max-assoc zero (suc n) (suc p) = refl
max-assoc (suc m) zero zero = refl
max-assoc (suc m) zero (suc p) = refl
max-assoc (suc m) (suc n) zero = refl
max-assoc (suc m) (suc n) (suc p) = cong suc (max-assoc m n p)

max-idemp : (m : ℕ) → m max m ≡ m
max-idemp zero = refl
max-idemp (suc m) = cong suc (max-idemp m)

max-comm : (m n : ℕ) → m max n ≡ n max m
max-comm zero zero = refl
max-comm zero (suc n) = refl
max-comm (suc m) zero = refl
max-comm (suc m) (suc n) = cong suc (max-comm m n) 

+-distribˡ : (m n p : ℕ) → m + (n max p) ≡ m + n max m + p
+-distribˡ zero zero zero = refl
+-distribˡ zero zero (suc p) = refl
+-distribˡ zero (suc n) zero = refl
+-distribˡ zero (suc n) (suc p) = +-distribˡ 1 n p
+-distribˡ (suc m) zero zero = cong suc (+-distribˡ m zero zero)
+-distribˡ (suc m) zero (suc p) = cong suc (+-distribˡ m zero (suc p))
+-distribˡ (suc m) (suc n) zero = cong suc (+-distribˡ m (suc n) zero)
+-distribˡ (suc m) (suc n) (suc p) = cong suc (+-distribˡ m (suc n) (suc p))

 
-- 4.

{-
Prove (for natural numbers) that (m + n) ^ 2 = m ^ 2 + 2 * mn + n ^ 2.

Here you may want to use chain-of-equalities syntax.
    
You should not need to directly use the definitions of _+_ and _*_,
only their properties (so do not pattern-match on m or n).  But the
definitions of 2 and _^_ are needed.  -}
  
sq-+ : (m n : ℕ) →  (m + n) ^ 2 ≡ m ^ 2 + (2 * (m * n) + n ^ 2)
sq-+ m n = {! !}
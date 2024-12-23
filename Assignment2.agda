module Assignment2 where

open import PropositionalEquality
open import Logic
open import Nat
open import List
open import Sorting



-- 1.

{-

Given two lists xs = [x0, x1, ..., xm] and ys = [y0, y1, ..., yn] of natural numbers, 
we say that xs is lexicographically smaller than or equal to ys (written xs ≤lex ys) if 
- xs is empty, or 
- they are both non-empty and x0 ≡ y0 and the tail [x1, ..., xm] of xs is lexicographically 
  smaller than or equal to the tail [y1, ..., yn] of ys, or
- they are both non-empty and x0 < y0 (meaning x0 ≤ x1 but also ¬ x0 ≡ x1).

Make an inductive predicate for lexicograhic order. 

-}

infix 3 _≤lex_

data _≤lex_ : List ℕ → List ℕ → Set where
  {- declare the constructors! -}
  nil : {xs : List ℕ} → [] ≤lex xs
  eq : {x : ℕ} → {xs ys : List ℕ} → xs ≤lex ys → x ∷ xs ≤lex x ∷ ys 
  lt : {x y : ℕ} → {xs ys : List ℕ} → x ≤ y → ¬ x ≡ y → x ∷ xs ≤lex y ∷ ys
  
-- 2. 

{- 

Prove that lexicographic order is a partial order, that is, it is 
- reflexivity
- transitive
- antisymmetric 

<-trans is a useful lemma about the strict version < of the order ≤.

-}

≤lex-refl : {xs : List ℕ} → xs ≤lex xs
≤lex-refl {[]} = nil
≤lex-refl {x₁ ∷ xs} = eq ≤lex-refl 

<-trans : {x y z : ℕ} → x ≤ y → ¬ x ≡ y → y ≤ z → ¬ x ≡ z
<-trans z≤n n z≤n refl = n refl
<-trans (s≤s p) n (s≤s q) refl = ⊥-elim (n (≤-antisym (s≤s p) (s≤s q)))

≤lex-trans : {xs ys zs : List ℕ} → xs ≤lex ys → ys ≤lex zs → xs ≤lex zs
≤lex-trans nil nil = nil
≤lex-trans nil (eq q) = nil
≤lex-trans nil (lt x₁ x₂) = nil
≤lex-trans (eq p) (eq q) = eq (≤lex-trans p q)
≤lex-trans (eq p) (lt x₁ x₂) = lt x₁ x₂
≤lex-trans (lt x₁ x₂) (eq q) = lt x₁ x₂
≤lex-trans (lt x₁ x₂) (lt x₃ x₄) = lt (≤-trans x₁ x₃) (<-trans x₁ x₂ x₃)

≤lex-antisym : {xs ys : List ℕ} → xs ≤lex ys → ys ≤lex xs → xs ≡ ys
≤lex-antisym nil nil = refl
≤lex-antisym (eq p) (eq q) = cong (_∷_ _) (≤lex-antisym p q)
≤lex-antisym (eq p) (lt x₁ x₂) = (⊥-elim (x₂ refl))
≤lex-antisym (lt x₁ x₂) (eq q) = (⊥-elim (x₂ refl))
≤lex-antisym (lt x₁ x₂) (lt x₃ x₄) = ⊥-elim (x₄ (≤-antisym x₃ x₁))

-- 3. 

{-

Prove the following interplay between lexicographic order and appending: 
- if xs ≤ ys then xs ≤ ys ++ zs for all zs, 
- if ys ≤ zs then xs ++ ys ≤ xs ++ zs for all xs. 

-}

≤lex-++ : {xs ys zs : List ℕ} → xs ≤lex ys → xs ≤lex ys ++ zs
≤lex-++ nil = nil
≤lex-++ (eq p) = eq (≤lex-++ p)
≤lex-++ (lt x₁ x₂) = lt x₁ x₂


++-≤lex : {xs ys zs : List ℕ} → ys ≤lex zs → xs ++ ys ≤lex xs ++ zs
++-≤lex {[]} nil = nil
++-≤lex {x₁ ∷ xs} nil = eq (++-≤lex nil)
++-≤lex {[]} (eq p) = ++-≤lex p
++-≤lex {x₁ ∷ xs} (p) = eq (++-≤lex p)
++-≤lex {[]} (lt x₁ x₂) = lt x₁ x₂


-- 4. 

{-

Prove that, for any list xs, the insertion sort of xs is lexicographically smaller 
than or equal to xs.

This is provable with a lemma about insert.

-}

insert-≤lex : (x : ℕ) → (xs : List ℕ) → insert x xs ≤lex x ∷ xs
insert-≤lex x [] = eq nil
insert-≤lex x (x₁ ∷ xs) with x ≤? x₁
... | yes p = eq (eq ≤lex-refl)
... | no p = lt (≤-total p) ({! !})

sort-≤lex : (xs : List ℕ) → insertion-sort xs ≤lex xs
sort-≤lex [] = nil
sort-≤lex (x₁ ∷ xs) = {!  !} 


{-

Below is another (more complicated) algorithm-agnostic strategy that
does not need decidability of the order, involving more lemmas.

≈-ne : {y : ℕ} → {ys : List ℕ} → ¬ ([] ≈ y ∷ ys)
≈-ne q = {!!} 

≤all-∈ : {x y : ℕ} → {ys : List ℕ} → y ∈ ys → x ≤all ys → x ≤ y
≤all-∈ p q = {!!} 

≈-∈ : {x : ℕ} → {xs ys : List ℕ} → x ∈ xs → xs ≈ ys → x ∈ ys
≈-∈ p q = {!!} 

≈-remove :  {x : ℕ} → {xs ys : List ℕ} → (p : x ∈ xs) → (q : xs ≈ ys) →
                                                 removeGiven xs p ≈ removeGiven ys (≈-∈ p q)
≈-remove p q = {!!} 

≈-∷-remove : {x : ℕ} → {xs : List ℕ} → (p : x ∈ xs) → x ∷ removeGiven xs p ≈ xs
≈-∷-remove p = {!!}

≈-sorted-hd : {x y : ℕ} → {xs ys : List ℕ} → x ∈ xs → xs ≈ y ∷ ys → Sorted (y ∷ ys) → y ≤ x
≈-sorted-hd p q s = {!!} 

≈-tl : {x : ℕ} → {xs ys : List ℕ} → (p : x ∈ xs) → xs ≈ x ∷ ys → removeGiven xs p ≈ ys
≈-tl p q = {!!}

≈-sorted-≤lex : {xs ys : List ℕ} → xs ≈ ys → Sorted ys → ys ≤lex xs
≈-sorted-≤lex {xs} {ys} q s = {!!} 
      
-}    

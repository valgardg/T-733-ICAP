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
    -- Case 1: Two empty lists are trivially lexicographically equal
  lexEq : (xs : List ℕ) → xs ≤lex xs
  
  -- Case 2: An empty list is less than any non-empty list
  lexLtEmpty : (xs ys : List ℕ) → xs ≤lex (y ∷ ys)

  -- Case 3: If the head elements are equal, recurse on the tails
  lexEqTail : (x y : ℕ) → (xs ys : List ℕ) → x ≡ y → xs ≤lex ys → x ∷ xs ≤lex y ∷ ys

  -- Case 4: If the head of the first list is smaller, then the first list is less
  lexLtHead : (x y : ℕ) → (xs ys : List ℕ) → x ≤ y → x ∷ xs ≤lex y ∷ ys


  
-- 2. 

{- 

Prove that lexicographic order is a partial order, that is, it is 
- reflexivity
- transitive
- antisymmetric 

<-trans is a useful lemma about the strict version < of the order ≤.

-}

≤lex-refl : {xs : List ℕ} → xs ≤lex xs
-- ≤lex-refl {xs} = {!!} 
≤lex-refl {xs} = lexEq xs

<-trans : {x y z : ℕ} → x ≤ y → ¬ x ≡ y → y ≤ z → ¬ x ≡ z
<-trans p n q r = {!!}



≤lex-trans : {xs ys zs : List ℕ} → xs ≤lex ys → ys ≤lex zs → xs ≤lex zs
≤lex-trans p q = {!!} 

≤lex-antisym : {xs ys : List ℕ} → xs ≤lex ys → ys ≤lex xs → xs ≡ ys
-- ≤lex-antisym p q = {!!}

-- 3. 

{-

Prove the following interplay between lexicographic order and appending: 
- if xs ≤ ys then xs ≤ ys ++ zs for all zs, 
- if ys ≤ zs then xs ++ ys ≤ xs ++ zs for all xs. 

-}

≤lex-++ : {xs ys zs : List ℕ} → xs ≤lex ys → xs ≤lex ys ++ zs
≤lex-++ p = {!!} 


++-≤lex : {xs ys zs : List ℕ} → ys ≤lex zs → xs ++ ys ≤lex xs ++ zs
++-≤lex {xs} p = {!!}


-- 4. 

{-

Prove that, for any list xs, the insertion sort of xs is lexicographically smaller 
than or equal to xs.

This is provable with a lemma about insert.

-}

insert-≤lex : (x : ℕ) → (xs : List ℕ) → insert x xs ≤lex x ∷ xs
insert-≤lex x xs = {!!}

sort-≤lex : (xs : List ℕ) → insertion-sort xs ≤lex xs
sort-≤lex xs = {!!} 

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
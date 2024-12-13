-- Intro to computer-assisted proof

-- Insertion sorting 

module Sorting where

open import PropositionalEquality
open import Logic
open import List
open import Nat 



-- insertion-sort

insert : ℕ → List ℕ → List ℕ
insert x [] = [ x ]
insert x (y ∷ ys) with x ≤? y
...  | yes _ = x ∷ y ∷ ys
...  | no _  = y ∷ insert x ys

insertion-sort : List ℕ → List ℕ
insertion-sort [] = []
insertion-sort (x ∷ xs) = insert x (insertion-sort xs)



-- insertion-sort sorts

data _≤all_ (x : ℕ) : List ℕ → Set where
  [] : x ≤all []
  _∷_ : {y : ℕ} → {ys : List ℕ} → x ≤ y → x ≤all ys → x ≤all (y ∷ ys)

≤all-trans : {x y : ℕ} → {zs : List ℕ} → x ≤ y → y ≤all zs → x ≤all zs
≤all-trans _ [] = []
≤all-trans p (q ∷ qs) =  ≤-trans p q  ∷ ≤all-trans p qs

data Sorted : List ℕ → Set where
  []  : Sorted []
  _∷_ : {x : ℕ} → {xs : List ℕ} → x ≤all xs → Sorted xs → Sorted (x ∷ xs)

≤all-insert : {x y : ℕ} → {zs : List ℕ} → x ≤ y → x ≤all zs → x ≤all insert y zs
≤all-insert p [] = p ∷ []
≤all-insert {_} {y} {z ∷ zs} p (q ∷ qs) with y ≤? z
...  | yes _ = p ∷ q ∷ qs
...  | no _  = q ∷ ≤all-insert p qs

insert-preserves-sorted : (x : ℕ) → (xs : List ℕ) →
       Sorted xs → Sorted (insert x xs)
insert-preserves-sorted x [] [] = [] ∷ []
insert-preserves-sorted x (y ∷ ys) (q ∷ qs) with x ≤? y
... | yes r = ((r  ∷ ≤all-trans r q )) ∷ (q ∷ qs)
... | no r = ≤all-insert (≤-total r) q  ∷  insert-preserves-sorted x ys qs 


insertion-sort-sorts : (xs : List ℕ) → Sorted (insertion-sort xs)
insertion-sort-sorts [] = []
insertion-sort-sorts (x ∷ xs) = insert-preserves-sorted x (insertion-sort xs) (insertion-sort-sorts xs) 



-- Insertion-sort permutes

{-
≈ is entered as \approx
-}


infix 4 _≈_ 

data _≈_ : List ℕ → List ℕ → Set where
  ≈[] : [] ≈ []
  cong∷ : {x : ℕ} → {xs ys : List ℕ} → xs ≈ ys → x ∷ xs ≈ x ∷ ys
  swap : {x y : ℕ} → {ys : List ℕ} → x ∷ y ∷ ys ≈ y ∷ x ∷ ys 
  ≈-trans : {xs ys zs : List ℕ} → xs ≈ ys → ys ≈ zs → xs ≈ zs

≈-refl : {xs : List ℕ} → xs ≈ xs
≈-refl {[]} = ≈[]
≈-refl {x ∷ xs} = cong∷ (≈-refl {xs})  


{-
data _≈_ : List ℕ → List ℕ → Set where
  ≈-refl : {xs : List ℕ} → xs ≈ xs
  swap : {x y : ℕ} → {zs ys : List ℕ} → zs ++ x ∷ y ∷ ys ≈ zs ++ y ∷ x ∷ ys 
  ≈-trans : {xs ys zs : List ℕ} → xs ≈ ys → ys ≈ zs → xs ≈ zs
-}


insert-permutes : (x : ℕ) → (ys : List ℕ) → x ∷ ys ≈ insert x ys
insert-permutes x [] = cong∷ ≈[]
insert-permutes x (y ∷ ys) with x ≤? y
... | yes p = ≈-refl
... | no p = ≈-trans swap (cong∷ (insert-permutes x ys))  

insertion-sort-permutes : (xs : List ℕ) → xs ≈ insertion-sort xs
insertion-sort-permutes [] = ≈[]
insertion-sort-permutes (x ∷ xs) = ≈-trans (cong∷ (insertion-sort-permutes xs))
                                           (insert-permutes x (insertion-sort xs))  




-- mergesort 

evens : List ℕ → List ℕ
evens [] = []
evens (x ∷ []) = [ x ]
evens (x ∷ _ ∷ xs) = x ∷ evens xs

odds : List ℕ → List ℕ
odds [] = []
odds (x ∷ []) = []
odds (_ ∷ x ∷ xs) = x ∷ odds xs

{- 
If the following of merge gives a termination-check error with 
your version of Agda, then put the pragma TERMINATING also here 
and before the definitions of ≤all-merge and merge-preserves-sorted
below.
-}
{-# TERMINATING #-}
merge : List ℕ → List ℕ → List  ℕ
merge [] ys = ys
merge (x ∷ xs) [] = x ∷ xs
merge (x ∷ xs) (y ∷ ys) with x ≤? y
... | yes _ = x ∷ merge xs (y ∷ ys)
... | no _ = y ∷ merge (x ∷ xs) ys 


{-# TERMINATING #-}
{- The termination checker does not accept this definition.
To convince the termination checker, 
a finer definition is needed. 
-}
mergesort : List  ℕ → List  ℕ
mergesort [] = []
mergesort (x ∷ [])  = [ x ]
mergesort (x ∷ x' ∷ xs) =  merge (mergesort (x ∷ evens xs)) (mergesort (x' ∷ odds xs))


{-# TERMINATING #-}
≤all-merge : {x : ℕ} → {ys zs : List ℕ} → x ≤all ys → x ≤all zs → x ≤all merge ys zs
≤all-merge {x} {[]} {zs} _ q = q
≤all-merge {x} {y ∷ ys} {[]} p _ = p 
≤all-merge {x} {y ∷ ys} {z ∷ zs} (p ∷ ps) (q ∷ qs) with y ≤? z
... | yes _ =  p ∷ ≤all-merge ps (q ∷ qs)
... | no _  =  q ∷ ≤all-merge (p ∷ ps) qs 

{-# TERMINATING #-}
merge-preserves-sorted : (xs ys : List ℕ) → Sorted xs → Sorted ys → Sorted (merge xs ys)
merge-preserves-sorted [] ys _ q = q
merge-preserves-sorted (x ∷ xs) [] p _ = p
merge-preserves-sorted (x ∷ xs) (y ∷ ys) (p ∷ ps) (q ∷ qs)  with x ≤? y
... | yes r = ≤all-merge p (r ∷ ≤all-trans r q) ∷ merge-preserves-sorted xs (y ∷ ys) ps (q ∷ qs)  
... | no r =  ≤all-merge (≤-total r ∷ ≤all-trans (≤-total r) p) q  ∷ merge-preserves-sorted (x ∷ xs) ys (p ∷ ps) qs 
 

{-# TERMINATING #-}
mergesort-sorts : (xs : List ℕ) → Sorted (mergesort xs)
mergesort-sorts [] = []
mergesort-sorts (x ∷ []) =  [] ∷ [] 
mergesort-sorts (x ∷ x' ∷ xs)
           = merge-preserves-sorted
                    (mergesort (x ∷ evens xs)) (mergesort (x' ∷ odds xs))
                    (mergesort-sorts (x ∷ evens xs)) (mergesort-sorts (x' ∷ odds xs))  

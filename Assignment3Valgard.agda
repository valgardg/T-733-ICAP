{-# OPTIONS --allow-unsolved-metas #-}

module Assignment3Valgard where

open import PropositionalEquality
open import Logic
open import Nat
open import Bool

open import BST


{-

Assignment 3, ICAP, autumn 2024, deadline Tue 17 Dec 2024 23:59

-}



-- 1.

{-

Write a function rotate-right that rotates a given tree to the right
by one step if possible.

That is, given a tree that has a value m at the root and another value
m' at the root of the left child subtree, the value m' should end up
at the root and the other value and the subtrees move around suitable. 

Trees that don't have these two values present should be left
unchanged.

Prove that that rotate-right preserves the isBST property.

Prove that a given tree and its rotated version contain the same values. 

-} 

rotate-right : Tree → Tree
rotate-right lf = lf
rotate-right (br nv lf rs) = (br nv lf rs)
rotate-right (br nv (br x₁ ls ls₁) rs) = (br x₁ ls (br nv ls₁ rs))

rotate-right-preserves-isBST : (t : Tree) → t isBST → rotate-right t isBST
rotate-right-preserves-isBST t lfB = lfB
rotate-right-preserves-isBST t (brB x₁ x₂ lfB tbst₁) = brB x₁ x₂ lfB tbst₁
rotate-right-preserves-isBST t (brB x₁ x₂ (brB x₃ x₄ tbst tbst₂) tbst₁) = brB x₃ {!  !} tbst (brB {!  !} x₂ tbst₂ tbst₁)

-- rotate-right-preserves-isBST t lfB = lfB
-- rotate-right-preserves-isBST t (brB x₁ x₂ lfB tbst₁) = brB x₁ x₂ lfB tbst₁
-- rotate-right-preserves-isBST t (brB x₁ x₂ (brB x₃ x₄ tbst tbst₂) tbst₁) = brB x₃ {! !} tbst (brB {!  !} x₂ tbst₂ tbst₁)

rotate-right-preserves-∈ : (n : ℕ) → (t : Tree) → n ∈ t → n ∈ rotate-right t
rotate-right-preserves-∈ n (br x₁ lf t₁) n∈t = n∈t
rotate-right-preserves-∈ n (br x₁ (br x₂ t t₂) t₁) here = right here
rotate-right-preserves-∈ n (br x₁ (br x₂ t t₂) t₁) (left here) = here
rotate-right-preserves-∈ n (br x₁ (br x₂ t t₂) t₁) (left (left n∈t)) = left n∈t
rotate-right-preserves-∈ n (br x₁ (br x₂ t t₂) t₁) (left (right n∈t)) = right (left n∈t)
rotate-right-preserves-∈ n (br x₁ (br x₂ t t₂) t₁) (right n∈t) = right (right n∈t) 

rotate-right-reflects-∈ : (n : ℕ) → (t : Tree) → n ∈ rotate-right t → n ∈ t
rotate-right-reflects-∈ n (br x₁ lf t₁) n∈rt = n∈rt
rotate-right-reflects-∈ n (br x₁ (br x₂ t t₂) t₁) here = left here
rotate-right-reflects-∈ n (br x₁ (br x₂ t t₂) t₁) (left n∈rt) = left (left n∈rt)
rotate-right-reflects-∈ n (br x₁ (br x₂ t t₂) t₁) (right here) = here
rotate-right-reflects-∈ n (br x₁ (br x₂ t t₂) t₁) (right (left n∈rt)) = left (right n∈rt)
rotate-right-reflects-∈ n (br x₁ (br x₂ t t₂) t₁) (right (right n∈rt)) = right n∈rt 


{-

For comparison, define rotate-right also for intrinsic BSTs.

-}

rotate-rightB : {d u : ℕ} → BST d u → BST d u
rotate-rightB lf = lf
rotate-rightB (br n lf t₁) = br n lf t₁
rotate-rightB (br n (br n₁ t t₂) t₁) = br n (br n₁ (rotate-rightB t) t₂) t₁ 

-- rotate-rightB lf = lf
-- rotate-rightB (br n lf t₁) = br n lf t₁
-- rotate-rightB (br n (br n₁ t t₂) t₁) = br n (br n₁ (rotate-rightB t) t₂) t₁ 

-- rotate-rightB : {d u : ℕ} → BST d u → BST d u
-- rotate-rightB lf = lf
-- rotate-rightB (br n t t₁) = br n (rotate-rightB t) t₁ 



-- 2.

{-

Below is a function floor for finding the least value in a given tree
t less-than-or-equal to a given value n. We call this value the floor
of n (it's the best underapproximation of n in the tree).

The function takes in also a value k. If n has no floor, the function
returns k -- so k serves as a "default" value. 

But k also functions as an accumulator in the function, it serves as
the (at every moment best known) lower bound for the floor of n.

-}

floor : ℕ → ℕ → Tree → ℕ
floor k n lf = k
floor k n (br m l r) with cmp n m
... | lt _ _ = floor k n l
... | eq _     = n
... | gt _ _ = floor m n r

{-

Prove these properties of the function floor.

-}

nrefl : (n : ℕ) → n ≤ n
nrefl n = ≤-refl

floor-monot : (k k' : ℕ) → k ≤ k' → (n : ℕ) → (t : Tree) → floor k n t ≤ floor k' n t 
floor-monot k k' k≤k' n lf = k≤k'
floor-monot k k' k≤k' n (br x₁ t t₁) with cmp n x₁
... | lt _ _ = floor-monot k k' k≤k' n t
... | eq _     = nrefl n
... | gt x₂ x₃ = floor-monot x₁ x₁ (nrefl x₁) n t₁

lb-floor : (k n : ℕ) → k ≤ n → (t : Tree) → All (_≤_ k) t → k ≤ floor k n t 
lb-floor k n k≤n lf k≤t = nrefl k
lb-floor k n k≤n (br x₁ t t₁) k≤t with cmp n x₁
lb-floor k n k≤n (br x₁ t t₁) (brA x₂ k≤t k≤t₁) | lt _ _ = lb-floor k n k≤n t k≤t -- All (_≤_ k) t
... | eq _   = k≤n
lb-floor k n k≤n (br x₁ t t₁) (brA x₄ k≤t k≤t₁) | gt x₂ _₃ = ≤-trans (lb-floor k n k≤n t₁ k≤t₁) (floor-monot k x₁ x₄ n t₁) -- floor k n t₁ ≤ floor x₁ n t₁

-- lb-floor k n k≤n (br x₁ t t₁) (brA x₄ k≤t k≤t₁) | gt x₂ _₃ = ≤-trans x₄ (lb-floor x₁ n x₂ t₁ {!  !})
-- lb-floor k n k≤n (br x₁ t t₁) (brA x₂ k≤t k≤t₁) | gt _ _ = ≤-trans x₂ (lb-floor x₁ n {!   !} {!   !} {!   !})


    -- lb-floor k {!   !} {!   !} (br n t₁ t₁) (brA k≤n k≤t₁ k≤t₁)

    -- k ≤ floor x₁ n t₁

floor-lb : (k n : ℕ) → k ≤ n → (t : Tree) → floor k n t ≤ n
floor-lb k n k≤n lf = k≤n
floor-lb k n k≤n (br x₁ t t₁) with cmp n x₁
... | lt _ _ = floor-lb k n k≤n t   
... | eq _     = nrefl n         
... | gt x₂ x₃ = floor-lb x₁ n x₂ t₁ 
# Type-free lambda calculus

This file contains the Agda formalization of some definitions and lemmas from Chapter 1 of the book on Curry-Howard isomorphism by Sørensen and Urzyczyn [[1]](#Ref-1).

Throughout this file we will use the following Agda elements from the libraries.

```agda
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
```

## Pre-terms

To define pre-terms we need a set of identifiers or variables.
This set must be countably infinite, and its elements must be comparable for equality.
For simplicity, we will use natural numbers as identifiers.

```agda
Variable : Set
Variable = ℕ
```

**Definition 1.2.1** from [[1]](#Ref-1) defines pre-terms as follows:

* Every variable is a pre-term.
* If `M`, `N` are pre-terms, then `(MN)` is a pre-term.
* If `x` is a variable and `M` is a pre-term, then `(λxM)` is a pre-term.

We can express this in Agda as the following data type.

```agda
-- Def. 1.2.1
data Preterm : Set where
  var : Variable → Preterm
  lam : Variable → Preterm → Preterm
  app : Preterm → Preterm → Preterm
```

The `Preterm` constructor `var` maps variables to preterms, the constructor `lam` constructs a lambda abstraction from a variable and a preterm, and the constructor `app` constructs an application from two preterms.

In this formalization we will NOT use the convention given as 1.2.2 in [[1]](#Ref-1) to omit parentheses in preterms.

For example, the preterm `(λx(xy))` will be represented as `lam x (app (var x) (var y))`, for `x = 0` and `y = 1` (or some other choice of variables).

```agda
λx-xy = let x = 0
            y = 1
         in lam x (app (var x) (var y))
```

## Free variables

An important notion in lambda calculus is that of free variable.
According to **Definition 1.2.3** from [[1]](#Ref-1), the set `FV(M)` of free variables of `M` is defined as follows.

* FV(x) = {x};
* FV(λxP) = FV(P) - {x} ;
* FV(PQ) = FV(P) U FV(Q).

We can express this in Agda as the following inductive family, providing a predicate to express whether a variable is free in a preterm.

```agda
-- Def. 1.2.3
data isFV : Variable → Preterm → Set where
  isFV-var : ∀ {x} 
             --------------------------------------------
             → isFV x (var x)
  isFV-lam : ∀ {x y P} 
             → x ≢ y
             → isFV x P
             --------------------------------------------
             → isFV x (lam y P)
  isFV-app₁ : ∀ {x P Q}
             → isFV x P
             --------------------------------------------
             → isFV x (app P Q)
  isFV-app₂ : ∀ {x P Q}
             → isFV x Q
             --------------------------------------------
             → isFV x (app P Q)
```

We may prove several properties about free variables.
```agda
lema-x∉fvλxP : ∀ {x P} → ¬ isFV x (lam x P)
lema-x∉fvλxP (isFV-lam x≢x _) = x≢x refl

lema-x∉fvλyP⇒x∉fvP : ∀ {x y P} → ¬ x ≡ y → ¬ isFV x (lam y P) → ¬ isFV x P
lema-x∉fvλyP⇒x∉fvP {x} {y} {P} ¬x≡y ¬x∈λyP x∈P = ¬x∈λyP (isFV-lam ¬x≡y x∈P)

lema-x∉fvPQ⇒x∉fvP : ∀ {x P Q} → ¬ isFV x (app P Q) → ¬ isFV x P
lema-x∉fvPQ⇒x∉fvP {x} {P} {Q} ¬x∈PQ x∈P = ¬x∈PQ (isFV-app₁ x∈P)

lema-x∉fvPQ⇒x∉fvQ : ∀ {x P Q} → ¬ isFV x (app P Q) → ¬ isFV x Q
lema-x∉fvPQ⇒x∉fvQ {x} {P} {Q} ¬x∈PQ x∈Q = ¬x∈PQ (isFV-app₂ x∈Q)
```

The first one establishes that a variable `x` is not free in the preterm `λxP`, for any preterm `P`.
The second one establishes that if a variable `x` is not free in `λyP`, where `x` and `y` are different variables, then `x` is not free in `P`.
The remaining lemmas establish that if a variable `x` is not free in an application, it is not free in any of its parts.

## Subterms

It is useful to define the notion of subterm, in order to reason on them, as follows.

```agda
data isSubterm : Preterm → Preterm → Set where
  isSubterm-refl : ∀ {M} → isSubterm M M
  isSubterm-app₁ : ∀ {L P Q} → isSubterm L P → isSubterm L (app P Q)
  isSubterm-app₂ : ∀ {L P Q} → isSubterm L Q → isSubterm L (app P Q)
  isSubterm-lam  : ∀ {L x P} → isSubterm L P → isSubterm L (lam x P)
```

There are also some useful lemmas about subterms.

```agda
lema-λxP-isNotSubtermOf-y : ∀ {x P y} → ¬ isSubterm (lam x P) (var y)
lema-λxP-isNotSubtermOf-y ()
```

## Substitutions

According to **Definition 1.2.4** from [[1]](#Ref-1), the substitution of a preterm `N` for a variable `x` in a preterm `M`, denoted by `M[x:=N]`, is defined only if no free variable of `N` becomes bound in `M[x:=N]`.
We may express that notion in Agda as follows.

```agda 
data _[_:=_]def : Preterm → Variable → Preterm → Set where
  isDef : ∀ {M x N} 
          → (∀ {y} {L} → isFV y N 
                       → isSubterm (lam y L) M 
                       → ¬ (isFV x (lam y L)))
          --------------------------------------------
          → M [ x := N ]def
```

```agda

lema-isDef-var₁ : ∀ {x N} → (var x) [ x := N ]def
lema-isDef-var₁ {x} {N} = isDef (λ {y} {L} y∈fvN λyL⊆x x∈λyL → lema-λxP-isNotSubtermOf-y λyL⊆x)

--   isDef-var₂ : ∀ {y x N} → (var y) [ x := N ]def
--   isDef-app  : ∀ {P Q x N} 
--                → P [ x := N ]def 
--                → Q [ x := N ]def 
--                --------------------------------------------
--                → app P Q [ x := N ]def
--   isDef-lam₁ : ∀ {P x N} → lam x P [ x := N ]def

lema-P[x:=N]def-and-Q[x:=N]def-implies-PQ[x:=N]def : ∀ {P Q x N} 
      → P [ x := N ]def 
      → Q [ x := N ]def 
      -----------------------------------------------
      → app P Q [ x := N ]def
lema-P[x:=N]def-and-Q[x:=N]def-implies-PQ[x:=N]def {P} {Q} {x} {N} P[x:=N]def Q[x:=N]def
  = {!   !}
--    with ( P[x:=N]def, Q[x:=N]def )
-- ... | ( isDef {P} {x} {N} PxN
--       , isDef QxN
--       ) = ? -- isDef (λ {y} {L} y∈fvN λyL⊆PQ x∈λyL → {!   !}) -- analyze {P} {Q} {x} {N} {y} {L} y∈fvN x∈λyL λyL⊆PQ)
    -- where analyze : ∀ {P Q x N y L} → isFV y N → isFV x (lam y L) → isSubterm (lam y L) (app P Q) -> Data.Empty.⊥
    --       analyze {P} {Q} {x} {N} {y} {L} y∈fvN x∈λyL λyL⊆PQ 
    --         with λyL⊆PQ
    --       ... | isSubterm-app₁ λyL⊆P = PxN {y} {L} {!   !} {!   !} {!   !}  -- y∈fvN λyL⊆P x∈λyL
    --       ... | isSubterm-app₂ λyL⊆Q = {!   !}

-- Def. 1.2.4
data _[_:=_]=_ : Preterm →  Variable →  Preterm →  Preterm →  Set where
  sub-var₁ : ∀ {x N} → (var x) [ x := N ]= N
  sub-var₂ : ∀ {x y N} → x ≢ y → var y [ x := N ]= var y
  sub-app : ∀ {P Q x N P' Q'}
            → P [ x := N ]= P'
            → Q [ x := N ]= Q'
            --------------------------------------------
            → app P Q [ x := N ]= app P' Q'
  sub-lam₁ : ∀ {P x N} → lam x P [ x := N ]= lam x P
  sub-lam₂ : ∀ {x y P N P'}
             → x ≢ y
             → P [ x := N ]= P'
             --------------------------------------------
             → lam y P [ x := N ]= lam y P'

lema-1-2-5-ia : ∀ {M x} → ¬ isFV x M → ∀ {N} → M [ x := N ]def
lema-1-2-5-ia {var z}   {x} ¬x∈fvz   {N} = 
    isDef {var z}   {x} {N} (λ {y} {L} _     λyL⊆z   _ → lema-λxP-isNotSubtermOf-y λyL⊆z)
lema-1-2-5-ia {lam z P} {x} ¬x∈fvλzP {N} = 
    isDef {lam z P} {x} {N} (λ {y} {L} y∈fvN λyL⊆λzP x∈λyL → {!   !})
lema-1-2-5-ia {app P Q} {x} ¬x∈fvPQ  {N} =
    isDef {app P Q} {x} {N} (λ {y} {L} y∈fvN λyL⊆fvPQ  x∈λyL → 
            let P[x:=N]def = lema-1-2-5-ia {P} {x} (lema-x∉fvPQ⇒x∉fvP ¬x∈fvPQ) {N}
                Q[x:=N]def = lema-1-2-5-ia {Q} {x} (lema-x∉fvPQ⇒x∉fvQ ¬x∈fvPQ) {N}
             in {!   !})

lema-1-2-5-ib : ∀ {x M} → ¬ isFV x M
         → ∀ {N} → Σ[ M' ∈ Preterm ] M [ x := N ]= M'
lema-1-2-5-ib {x} {var y}   ¬x∈fvy {N} 
   with x ≟ y
...  | yes refl = ( N , sub-var₁ )
...  | no  x≢y  = ( var y , sub-var₂ {x} {y} {N} x≢y )
lema-1-2-5-ib {x} {lam y P} ¬x∉fvyP {N}
   with x ≟ y
...  | yes refl = ( lam x P , sub-lam₁ )
...  | no  rr   =
   let ( P' , P[x:=N]=P') = lema-1-2-5-ib {x} {P} (λ { q → ¬x∉fvyP (isFV-lam rr q) }) {N}
    in ( lam y P' , sub-lam₂ rr P[x:=N]=P')
lema-1-2-5-ib {x} {app P Q} x∉fvPQ {N} = 
    let ( P' , P[x:=N]=P' ) = lema-1-2-5-ib {x} {P} (λ { r → x∉fvPQ (isFV-app₁ r) }) {N}
        ( Q' , Q[x:=N]=Q' ) = lema-1-2-5-ib {x} {Q} (λ { r → x∉fvPQ (isFV-app₂ r) }) {N}
     in ( app P' Q' , sub-app P[x:=N]=P' Q[x:=N]=Q' )


-- lema-1-2-5-i {x} {var y}     ¬x∉fvy {N}
--   with x ≟ y
-- ...  | yes refl = N , sub-var₁
-- ...  | no  x≢y  = var y , sub-var₂ x≢y
-- lema-1-2-5-i {x} {lam y t}   ¬x∉fvt {s}
--   with x ≟ y
-- ...  | yes refl = lam x t , sub-lam₁
-- ...  | no  p    =
--   let (t' , t[x:=s]=t') = lema-1-2-5-i {x} {t} (λ { q → ¬x∉fvt (isFV-lam p q) }) {s}
--    in lam y t' , sub-lam₂ p t[x:=s]=t'
-- lema-1-2-5-i {x} {app t₁ t₂} ¬x∉fvt {s} =
--   let (t₁' , t₁[x:=s]=t₁') = lema-1-2-5-i {x} {t₁} (λ { q → ¬x∉fvt (isFV-app₁ q) }) {s}
--       (t₂' , t₂[x:=s]=t₂') = lema-1-2-5-i {x} {t₂} (λ { q → ¬x∉fvt (isFV-app₂ q) }) {s}
--    in app t₁' t₂' , sub-app t₁[x:=s]=t₁' t₂[x:=s]=t₂'

-- _↔_ : Set → Set → Set
-- (A ↔ B) = (A → B) × (B → A)

-- lema-2a : ∀ {t x s t'}
--        → t [ x := s ]= t'
--        → ∀ {y}
--        → (isFV y t' → ((isFV y t × x ≢ y) ⊎ (isFV y s × isFV x t)))
-- lema-2a sub-var₁               y∈fvs    = inj₂ (y∈fvs , isFV-var)
-- lema-2a (sub-var₂ {x} {z} x≢z) isFV-var = inj₁ (isFV-var , x≢z)
-- lema-2a {_} {x} (sub-app t₁[x:=s]=t₁' t₂[x:=s]=t₂') (isFV-app₁ y∈fvt₁')
--   with lema-2a t₁[x:=s]=t₁' y∈fvt₁'
-- ... | inj₁ (y∈fvt₁ , x≢y)   = inj₁ (isFV-app₁ y∈fvt₁ , x≢y)
-- ... | inj₂ (y∈fvs , x∈fvt₁) = inj₂ (y∈fvs , isFV-app₁ x∈fvt₁)
-- lema-2a (sub-app t₁[x:=s]=t₁' t₂[x:=s]=t₂') (isFV-app₂ y∈fvt₂')
--   with lema-2a t₂[x:=s]=t₂' y∈fvt₂'
-- ... | inj₁ (y∈fvt₂ , x≢y)   = inj₁ (isFV-app₂ y∈fvt₂ , x≢y)
-- ... | inj₂ (y∈fvs , x∈fvt₂) = inj₂ (y∈fvs , isFV-app₂ x∈fvt₂)
-- lema-2a {_} {x} sub-lam₁ {y} y∈fvλxt
--   with x ≟ y
-- ... | yes refl = ⊥-elim (x-not-in-fv-lam-x y∈fvλxt)
-- ... | no  x≢y  = inj₁ (y∈fvλxt , x≢y)
-- lema-2a {_} {x} (sub-lam₂ {.x} {z} x≢z t[x:=s]=t') {y} (isFV-lam y≢z y∈fvt')
--   with lema-2a t[x:=s]=t' y∈fvt'
-- ... | inj₁ (y∈fvt , x≢y)   = inj₁ (isFV-lam y≢z y∈fvt , x≢y)
-- ... | inj₂ (y∈fvs , x∈fvt) = inj₂ (y∈fvs , isFV-lam x≢z x∈fvt)
```

# References 

<a name="Ref-1">[1]</a> Sørensen, M. H. and Urzyczyn, P. (2016). *Lectures on the Curry-Howard Isomorphism*. Elsevier.
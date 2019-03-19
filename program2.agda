module program2 where
open import Data.List using ([]; _∷_; List; length; reverse; map; foldr; downFrom)
open import Data.List.All using (All; []; _∷_; lookup)
open import Data.List.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Properties
  using (reverse-++-commute; map-compose; map-++-commute; foldr-++)

open import Data.Bool using (true; false; T; _∧_; _∨_; not) renaming (Bool to 𝔹)
open import Data.Nat using (ℕ; zero; suc; _*_; _∸_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import Data.Integer using (ℤ; _+_; _≤?_)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness; fromWitness)


data 𝕍 : Set where
  var : ℕ → 𝕍

infixr 20 _>>_


data Expr : Set where
  unit : Expr
  var : 𝕍 → Expr
  bool : 𝔹 → Expr
  loc : ℕ → Expr
  int : ℤ → Expr
  leq : Expr → Expr → Expr
  lispy-if : Expr → Expr → Expr → Expr
  assn : Expr → Expr → Expr
  malloc : Expr
  free : Expr
  _>>_ : Expr → Expr → Expr
  *_ : Expr → Expr



-- If we made Expr intrinsically typed, Store has to be pushed into Expr definition

data Val : Set where
  unit : Val
  int : ℤ → Val
  bool : 𝔹 → Val
  loc : ℕ → Val
  -- alias of a different variable
  -- var : 𝕍 → Val

  -- add get and set?


Ctx = List 𝕍
Store : Ctx → Set
-- never shrinks
Store = All (Function.const Val)


Heap : List ℕ → Set
-- can be freed
-- always returning maximum?
Heap = All (Function.const Val) 

data eval {c} {ln} (s : Store c) (h : Heap ln) : Expr → Val → Set where
  unit : eval s h unit unit
  int : ∀ {i} → eval s h (int i) (int i)
  bool : ∀ {b} → eval s h (bool b) (bool b)
  loc : ∀ {l} → eval s h (loc l) (loc l)
  var : ∀ {v} → (e : v ∈ c) → eval s h (var v) (lookup s e)
  leq : ∀ {n n' : ℤ} {e e'} →
        eval s h e (int n) →
        eval s h e' (int n') →
        eval s h e' (bool (⌊ n ≤? n' ⌋))
  lispy-if-true : ∀ {g e e'} {v} →
                  eval s h g (bool true) → 
                  eval s h e v →
                  eval s h (lispy-if g e e') v
  lispy-if-false : ∀ {g e e'} {v'} →
                   eval s h g (bool false) →
                   eval s h e' v' →
                   eval s h (lispy-if g e e') v'
  


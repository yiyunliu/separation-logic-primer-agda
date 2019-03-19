module program where
open import Data.List using ([]; _∷_; List; length; reverse; map; foldr; downFrom)
open import Data.List.All using (All; []; _∷_; lookup)
open import Data.List.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Properties
  using (reverse-++-commute; map-compose; map-++-commute; foldr-++)

open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import Data.Integer using (ℤ; _+_)

data Ty : Set where
  bool : Ty
  int  : Ty


Ctx = List Ty



data Expr (Γ : Ctx) : Ty → Set where
  bool : Bool → Expr Γ bool
  var : ∀ {t} → t ∈ Γ → Expr Γ t
  num : ℤ → Expr Γ int
  if : ∀ {t} → Expr Γ bool → Expr Γ t → Expr Γ t → Expr Γ t
  plus : Expr Γ int → Expr Γ int → Expr Γ int
  -- ref : ℕ → Expr Γ ()


data Val : Ty → Set where
  bool : Bool → Val bool
  num : ℤ → Val int
  -- ref : 


Env : Ctx → Set
Env Γ = All Val Γ

eval : ∀ {Γ t} → Expr Γ t → Env Γ → Val t
eval (bool x) env = bool x
eval (var x) env = lookup env x
eval (num x) env = num x
eval (if expr expr₁ expr₂) env with eval expr env
eval (if expr expr₁ expr₂) env | bool false = eval expr₂ env 
eval (if expr expr₁ expr₂) env | bool true = eval expr₁ env
eval (plus expr expr₁) env with eval expr env | eval expr₁ env
eval (plus expr expr₁) env | num x | num x₁ = num (x Data.Integer.+ x₁)

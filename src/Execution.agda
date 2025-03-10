module Execution where

open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.Product using (∃-syntax; _,_; _×_; proj₁)
open import Function.Base using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel; IsStrictPartialOrder; IsStrictTotalOrder)
open import Relation.Binary.Construct.Composition using (_;_)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Unary using (_⊆_)
open import Relation.Nullary using (¬_)

open import Event

open import Data.List.Membership.DecPropositional (_≟_) using (_∈_)

EventRel : List Event → Set₁
EventRel es = Rel (∃[ e ] e ∈ es) 0ℓ

record Execution : Set₁ where
  constructor execution
  field
    events : List Event

    poᵢₘₘ : EventRel events
    rmw : EventRel events

  po : EventRel events
  po = TransClosure poᵢₘₘ

  poloc : EventRel events
  poloc e@(W _ _ l _ , _) f@(W _ _ m _ , _) = (po e f) × l ≡ m
  poloc e@(W _ _ l _ , _) f@(R _ _ m _ , _) = (po e f) × l ≡ m
  poloc e@(R _ _ l _ , _) f@(W _ _ m _ , _) = (po e f) × l ≡ m
  poloc e@(R _ _ l _ , _) f@(R _ _ m _ , _) = (po e f) × l ≡ m

  poₜ : ℕ → EventRel events
  poₜ t e@(W u _ _ _ , _) f@(W v _ _ _ , _) = (po e f) × t ≡ u × t ≡ v
  poₜ t e@(W u _ _ _ , _) f@(R v _ _ _ , _) = (po e f) × t ≡ u × t ≡ v
  poₜ t e@(R u _ _ _ , _) f@(W v _ _ _ , _) = (po e f) × t ≡ u × t ≡ v
  poₜ t e@(R u _ _ _ , _) f@(R v _ _ _ , _) = (po e f) × t ≡ u × t ≡ v

record WellFormed : Set₁ where
  open Execution
  field
    exec : Execution
    poᵢₘₘ-isImmediate : {!!}
    po-isStrictPartialOrder : IsStrictPartialOrder ((_∘ proj₁) ∘ _<ᵢ_ ∘ proj₁) (po exec)
    poₜ-isStrictTotalOrder : ∀ t → IsStrictTotalOrder ((_∘ proj₁) ∘ _<ᵢ_ ∘ proj₁) (poₜ exec t)
    rmw⊆po : ∀ {e} → rmw exec e ⊆ poᵢₘₘ exec e
    rmw-RW : ∀ {t i l v u j m w n o p q} → ¬ rmw exec (W t i l v , n) (W u j m w , o) × ¬ rmw exec (W t i l v , n) (R u j m w , q) × ¬ rmw exec (R t i l v , p) (R u j m w , q)

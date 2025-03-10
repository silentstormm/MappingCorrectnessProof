module Event where

open import Data.Product using (_,_; _×_)
open import Data.Nat as Nat using (ℕ; _≤_; _<_)
open import Level using (0ℓ)
open import Relation.Binary using (DecidableEquality; Rel; IsStrictPartialOrder; IsStrictTotalOrder)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (_×-dec_; no; yes; contradiction)

data Event : Set where
  W : (thread id location value : ℕ) → Event
  R : (thread id location value : ℕ) → Event

_≟_ : DecidableEquality Event
(W t i l v) ≟ (W u j m w) with (t Nat.≟ u) ×-dec (i Nat.≟ j) ×-dec (l Nat.≟ m) ×-dec (v Nat.≟ w)
... | no ¬eq = no λ { refl → contradiction (refl , refl , refl , refl) ¬eq}
... | yes (refl , refl , refl , refl) = yes refl
(R t i l v) ≟ (R u j m w) with (t Nat.≟ u) ×-dec (i Nat.≟ j) ×-dec (l Nat.≟ m) ×-dec (v Nat.≟ w)
... | no ¬eq = no λ { refl → contradiction (refl , refl , refl , refl) ¬eq}
... | yes (refl , refl , refl , refl) = yes refl
(W _ _ _ _) ≟ (R _ _ _ _) = no λ ()
(R _ _ _ _) ≟ (W _ _ _ _) = no λ ()

data _≤ᵢ_ : Rel Event 0ℓ where
  refl-WW : ∀ {t i l v u j m w} → i ≤ j → (W t i l v) ≤ᵢ (W u j m w)
  refl-RW : ∀ {t i l v u j m w} → i ≤ j → (R t i l v) ≤ᵢ (W u j m w)
  refl-WR : ∀ {t i l v u j m w} → i ≤ j → (W t i l v) ≤ᵢ (R u j m w)
  refl-RR : ∀ {t i l v u j m w} → i ≤ j → (R t i l v) ≤ᵢ (R u j m w)

data _<ᵢ_ : Rel Event 0ℓ where
  refl-WW : ∀ {t i l v u j m w} → i < j → (W t i l v) <ᵢ (W u j m w)
  refl-RW : ∀ {t i l v u j m w} → i < j → (R t i l v) <ᵢ (W u j m w)
  refl-WR : ∀ {t i l v u j m w} → i < j → (W t i l v) <ᵢ (R u j m w)
  refl-RR : ∀ {t i l v u j m w} → i < j → (R t i l v) <ᵢ (R u j m w)

open import Function using (_∘_)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Unit.Polymorphic as Unit using (⊤; tt)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Product as Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)

open import Encoding.ST
open import Encoding.LeftoverST
open import Encoding.SplitST

module Encoding.LeftoverSplitST where


cancel-shared : ∀ {u} {s : S⟦ u ⟧} {Γ Δ : T⟦ s ⟧} → _≔_+_ {u} Γ Δ Γ → _≔_+_ {u} Δ Δ Δ
cancel-shared left = left
cancel-shared right = right
cancel-shared pure = pure
cancel-shared (chan sp₁ sp₂) = chan (cancel-shared sp₁) (cancel-shared sp₂)
cancel-shared [] = []
cancel-shared (sp ∷ sps) = (cancel-shared sp) ∷ (cancel-shared sps)

id-left : ∀ {u} {s : S⟦ u ⟧} {x : T⟦ s ⟧}
        → Σ[ id ∈ T⟦ s ⟧ ] _≔_+_ {u} x id x
id-left {session} = _ , right
id-left {type} {x = pure x , _} = _ , pure
id-left {type} {x = chan x , _} = _ , chan (proj₂ id-left) (proj₂ id-left)
id-left {ctx} {x = []} = _ , []
id-left {ctx} {x = _ ∷ _} = _ , proj₂ id-left ∷ proj₂ id-left

get-split : {s : S⟦ ctx ⟧} {Γ Θ : T⟦ s ⟧} {σ : C⟦ s ⟧}
          → Γ ⊢▹ Θ [ σ ] → Covered {ctx} σ Θ → Σ[ Δ ∈ T⟦ s ⟧ ] (_≔_+_ {ctx} Γ Δ Θ)
get-split (pure t v wt) c =
  Product.map (λ where (_ ∷ xs) → xs) (λ where (_ ∷ xs) → xs) (get-split wt (pure ∷ c))
get-split end c = id-left
get-split (new s wt) c =
  Product.map (λ where (_ ∷ xs) → xs) (λ where (_ ∷ xs) → xs) (get-split wt (chan used used ∷ c))
get-split (par wt x wt₁ x₁) c = {!!}
get-split (send x v x₁ x₂ wt) c = {!!}
get-split (recv x x₁) c = {!!}

leftover-to-split : {ss : S⟦ ctx ⟧} {Γ Δ Θ : T⟦ ss ⟧} {σ : C⟦ ss ⟧}
                  → _≔_+_ {u = ctx} Γ Δ Θ → Γ ⊢▹ Θ [ σ ] → Proc Δ
leftover-to-split split (pure t v wt) = {!!}
leftover-to-split split end = end (cancel-shared split)
leftover-to-split split (new s wt) = new s (leftover-to-split (chan left left ∷ split) wt)
leftover-to-split split (par pwt cp qwt cq) =
  par {!!} (leftover-to-split (proj₂ (get-split pwt cp)) pwt) (leftover-to-split (proj₂ (get-split qwt cq)) qwt)
leftover-to-split split (send x v x₁ x₂ wt) = send {!!} v {!!} {!!} {!!}
leftover-to-split split (recv x x₁) = recv {!!} {!!}

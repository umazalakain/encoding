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


cancel-shared : ∀ {u} {Γ Δ : T⟦ u ⟧} → _≔_+_ {u} Γ Δ Γ → _≔_+_ {u} Δ Δ Δ
cancel-shared left = left
cancel-shared right = right
cancel-shared pure = pure
cancel-shared (chan sp₁ sp₂) = chan (cancel-shared sp₁) (cancel-shared sp₂)
cancel-shared [] = []
cancel-shared (sp ∷ sps) = (cancel-shared sp) ∷ (cancel-shared sps)

id-left : ∀ {u} {x : T⟦ u ⟧} → Σ[ id ∈ T⟦ u ⟧ ] _≔_+_ {u} x id x
id-left {session} = _ , right
id-left {type} {x = pure x , _} = _ , pure
id-left {type} {x = chan x , _} = _ , chan (proj₂ id-left) (proj₂ id-left)
id-left {ctx} {x = []} = _ , []
id-left {ctx} {x = _ ∷ _} = _ , proj₂ id-left ∷ proj₂ id-left

rotate : ∀ {u} {x y z v w : T⟦ u ⟧}
       → _≔_+_ {u} x y z → _≔_+_ {u} z v w
       → Σ[ r ∈ T⟦ u ⟧ ] (_≔_+_ {u} x r w × _≔_+_ {u} r y v)
rotate left left = _ , left , left
rotate left right = _ , left , left
rotate right left = _ , left , right
rotate right right = _ , right , left
rotate pure pure = _ , pure , pure
rotate (chan xyzₗ xyzᵣ) (chan zvwₗ zvwᵣ) =
  let _ , spaₗ , spbₗ = rotate xyzₗ zvwₗ
      _ , spaᵣ , spbᵣ = rotate xyzᵣ zvwᵣ
   in _ , chan spaₗ spaᵣ , chan spbₗ spbᵣ 
rotate [] zvw = {!!}
rotate (xyz ∷ xyz₁) zvw = {!!}

get-split : {Γ Θ : T⟦ ctx ⟧} → Γ ⊢▹ Θ → Covered {ctx} Γ Θ → Σ[ Δ ∈ T⟦ ctx ⟧ ] (_≔_+_ {ctx} Γ Δ Θ)
get-split (pure t v wt) c = Product.map
  (λ where (_ ∷ xs) → xs)
  (λ where (_ ∷ xs) → xs)
  (get-split wt (pure ∷ c))
get-split end c = id-left
get-split (new s wt) c = Product.map
  (λ where (_ ∷ xs) → xs)
  (λ where (_ ∷ xs) → xs)
  (get-split wt (chan used used ∷ c))
get-split (par wtp cp wtq cq) c =
  let _ , spp = get-split wtp cp
      _ , spq = get-split wtq cq
      _ , sp , _ = rotate spp spq
   in _ , sp
get-split (send x v x₁ x₂ wt) c = {!!}
get-split (recv x x₁) c = {!!}

leftover-to-split : {Γ Δ Θ : T⟦ ctx ⟧} → _≔_+_ {ctx} Γ Δ Θ → Γ ⊢▹ Θ → Proc Δ
leftover-to-split split (pure t v wt) = {!!}
leftover-to-split split end = end (cancel-shared split)
leftover-to-split split (new s wt) = new s (leftover-to-split (chan left left ∷ split) wt)
leftover-to-split split (par pwt cp qwt cq) =
  par {!!} (leftover-to-split (proj₂ (get-split pwt cp)) pwt) (leftover-to-split (proj₂ (get-split qwt cq)) qwt)
leftover-to-split split (send x v x₁ x₂ wt) = send {!!} v {!!} {!!} {!!}
leftover-to-split split (recv x x₁) = recv {!!} {!!}

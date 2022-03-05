open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Function using (_∘_; _$_)
open import Data.Unit using (⊤; tt)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)


open import LinearPi

replrecv : ∀ {xs ys zs} → xs ≔ zs + ys → Null ys → (n : ℕ) → (t : ⟦ repl (pure ⊤) n ⟧ₜ) → Term zs (prod (pure ℕ) (repl (pure ⊤)) , (n , t)) → Process xs
replrecv sp null zero t term = end (Null-+ (+-comm sp) null (Null-Term (prod pure pure) term))
replrecv {_} {ys} sp null (suc n) t term =
  let (i , sp' , ni) = +-idˡ ys in
  let (i' , spi , nii) = +-idˡ i in
  letprod sp term
  (recv (pure ∷ chan #1-left #0 ∷ sp') (var (there pure (here ni (chan #1 #0 refl)))) λ where
    (tt , t') →
      let (_ , sp'' , ni') = +-idʳ (repl (pure ⊤) n , t') in
      let (_ , sp''' , ni'') = +-idˡ (repl (pure ⊤) n , t') in
      letprod (prod-left ∷ pure ∷ chan #0 #0 ∷ sp') (var (here (pure ∷ chan #0 #0 ∷ ni) prod))
      (replrecv (pure ∷ sp'' ∷ pure ∷ pure ∷ chan #0 #0 ∷ sp') (pure ∷ ni'' ∷ pure ∷ pure ∷ chan #0 #0 ∷ null) n t' (pair (pure ∷ sp''' ∷ pure ∷ pure ∷ chan #0 #0 ∷ spi) (pure n (pure ∷ ni'' ∷ pure ∷ pure ∷ chan #0 #0 ∷ nii)) (var (there pure (here (pure ∷ pure ∷ chan #0 #0 ∷ ni) (⊆-repl _)))))))

_ : Process ((chan #1 #1 (prod (pure ℕ) (repl (pure ⊤))) , tt) ∷ [])
_ = par (chan #1-left #1-right ∷ [])
  (recv
    (chan #1-left #0 ∷ [])
    (var (here [] (chan #1 #0 refl)))
    λ (n , c) → replrecv
      (prod-left ∷ chan #0 #0 ∷ [])
      (pure ∷ (chan #0 #0 ∷ []))
      n
      c
      (var (here (chan #0 #0 ∷ []) prod)))
  (new #1 #1 (prod (pure ⊤) (λ _ → pure ⊤)) $
    send
      (chan #1-left #1-right ∷ chan #0 #1-right ∷ [])
      (pair (chan #1-right #0 ∷ chan #0 #0 ∷ []) (pure 1 (chan #0 #0 ∷ (chan #0 #0 ∷ []))) (var (here (chan #0 #0 ∷ []) (chan #1 #0 refl))))
      (chan #0 #1-right ∷ (chan #0 #1-left ∷ []))
      (var (there (chan #0 #0 ) (here [] (chan #0 #1 refl)))) $
      send
        (chan #0 #1-right ∷ chan #0 #0 ∷ [])
        (pair (chan #0 #0 ∷ (chan #0 #0 ∷ [])) (pure tt (chan #0 #0 ∷ (chan #0 #0 ∷ []))) (pure tt (chan #0 #0 ∷ (chan #0 #0 ∷ []))))
        (chan #0 #1-left ∷ (chan #0 #0 ∷ []))
        (var (here (chan #0 #0 ∷ []) (chan #0 #1 refl)))
        (end (chan #0 #0 ∷ (chan #0 #0 ∷ []))))

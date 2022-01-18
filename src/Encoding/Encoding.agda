open import Function using (_∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product as Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List.Base as List

import SessionPi as S
import LinearPi as L


mutual
  ⟦_⟧ₑ-type : S.Type → L.Type
  ⟦ S.pure x ⟧ₑ-type = L.pure x
  ⟦ S.chan x ⟧ₑ-type = ⟦ x ⟧ₑ-session

  ⟦_⟧ₑ-session : S.Session → L.Type
  ⟦ S.end ⟧ₑ-session = L.chan L.0∙ L.0∙ (L.pure ⊤)
  ⟦ S.recv T C ⟧ₑ-session = L.chan L.1∙ L.0∙ (L.prod ⟦ T ⟧ₑ-type (⟦_⟧ₑ-session ∘ C ∘ decode T))
  ⟦ S.send T C ⟧ₑ-session = L.chan L.0∙ L.1∙ (L.prod ⟦ T ⟧ₑ-type (⟦_⟧ₑ-session ∘ C ∘ decode T))

  ⟦_⟧ₑ-ctx : S.Ctx → L.Ctx
  ⟦_⟧ₑ-ctx = List.map λ (T , t) → ⟦ T ⟧ₑ-type , encode T t

  decode : ∀ T → L.⟦ ⟦ T ⟧ₑ-type ⟧ₜ → S.⟦ T ⟧ₜ
  decode (S.pure A) x = x
  decode (S.chan x₁) _ = tt

  encode : ∀ T → S.⟦ T ⟧ₜ → L.⟦ ⟦ T ⟧ₑ-type ⟧ₜ
  encode (S.pure A) x = x
  encode (S.chan S.end) _ = tt
  encode (S.chan (S.recv T _)) _ = tt
  encode (S.chan (S.send T _)) _ = tt


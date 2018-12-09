module Maybe where

open import Prelude

data Maybe (a : Set) : Set where
  Just : a -> Maybe a
  Nothing : Maybe a

-- When we run Partial, we get a Maybe.
liftJust : {a : Set} -> (a -> Set) -> (Maybe a -> Set)
liftJust P Nothing = ⊥
liftJust P (Just x) = P x

instance
  Monad-Maybe : IsMonad Maybe
  Monad-Maybe = isMonad bind' Just refl
    where
    bind' : ∀ {a b} → Maybe a → (a → Maybe b) → Maybe b
    bind' (Just x) f = f x
    bind' Nothing f = Nothing

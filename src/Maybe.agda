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
  IsMonad.bind Monad-Maybe (Just x) f = f x
  IsMonad.bind Monad-Maybe Nothing f = Nothing
  IsMonad.pure Monad-Maybe x = Just x
  IsMonad.left-identity Monad-Maybe = refl

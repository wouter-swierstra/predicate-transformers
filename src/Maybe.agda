module Maybe where

open import Prelude

data Maybe (a : Set) : Set where
  Just : a -> Maybe a
  Nothing : Maybe a

-- When we run Partial, we get a Maybe.
liftJust : {a : Set} -> (a -> Set) -> (Maybe a -> Set)
liftJust P Nothing = ⊥
liftJust P (Just x) = P x

fmap : {a b : Set} -> (f : a -> b) -> Maybe a -> Maybe b
fmap f Nothing = Nothing
fmap f (Just x) = Just (f x)

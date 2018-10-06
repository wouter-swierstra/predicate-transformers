module WP where

wp : {a : Set} {b : a -> Set}
  -> (P : (x : a) -> b x -> Set)
  -> (f : (x : a) -> b x)
  -> (x : a) -> Set
wp P f x = P x (f x)

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Types.Classes where

import Plutarch.Prelude

class ScottConvertible (a :: PType) where
  type ScottOf a = (b :: PType) | b -> a
  toScott :: Term s a -> Term s (ScottOf a)
  fromScott :: Term s (ScottOf a) -> Term s a

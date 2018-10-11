module Ty where

import Data.String (IsString (..))

data Ty
    = Ty String
    | Ty :-> Ty
  deriving (Eq, Ord, Show)

infixr 1 :->

instance IsString Ty where fromString = Ty

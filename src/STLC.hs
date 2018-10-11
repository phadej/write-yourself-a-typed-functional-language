{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
module STLC where

import Bound
import Control.Monad (ap, guard)
import Data.String (IsString (..))
import Data.Functor.Classes

import Ty

-------------------------------------------------------------------------------
-- Syntax
-------------------------------------------------------------------------------

data Expr a
    = Var a
    | App (Expr a) (Expr a)
    | Lam Ty (Scope () Expr a)
  deriving (Functor, Foldable, Traversable)

instance Applicative Expr where
    pure  = return
    (<*>) = ap

instance Monad Expr where
    return = Var

    Var x   >>= k = k x
    App f x >>= k = App (f >>= k) (x >>= k)
    Lam t e >>= k = Lam t (e >>>= k)

instance IsString a => IsString (Expr a) where fromString = Var . fromString

instance Show1 Expr where
    liftShowsPrec sp _  d (Var x)   = showsUnaryWith sp "Var" d x
    liftShowsPrec sp sl d (App f x) = showsBinaryWith (liftShowsPrec sp sl) (liftShowsPrec sp sl) "App" d f x
    liftShowsPrec sp sl d (Lam t e) = showsBinaryWith showsPrec (liftShowsPrec sp sl) "Lam" d t e

instance Show a => Show (Expr a) where showsPrec = showsPrec1

lam :: Eq a => a -> Ty -> Expr a -> Expr a
lam x t e = Lam t (abstract1 x e)

-------------------------------------------------------------------------------
-- Typechecker
-------------------------------------------------------------------------------

-- | >>> typeCheck (const Nothing) (lam "x" "Int" "x" :: Expr String)
-- Just (Ty "Int" :-> Ty "Int")
--
typeCheck :: (a -> Maybe Ty) -> Expr a -> Maybe Ty
typeCheck ctx e = do
    et <- traverse ctx e
    go et
  where
    go :: Expr Ty -> Maybe Ty
    go (Var ty) = return ty
    go (Lam a x) = do
        b <- go (instantiate1 (Var a) x)
        return (a :-> b)
    go (App f x) = do
        ft <- go f
        case ft of
            a :-> b -> do
                xt <- go x
                guard (a == xt)
                return b
            _ -> fail "Function type expected"

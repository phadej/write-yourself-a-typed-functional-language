{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module BiSTLC where

import Bound.Var (Var (..), unvar)
import Bound.Scope (toScope)
import Bound.ScopeH
import Control.Monad (ap, guard)
import Control.Monad.Module
import Data.String (IsString (..))
import Data.Functor.Classes

import Ty
import qualified STLC as Uni

-------------------------------------------------------------------------------
-- Syntax
-------------------------------------------------------------------------------

data Syn a
    = Var a
    | App (Syn a) (Chk a)
    | Ann (Chk a) Ty
  deriving (Functor, Foldable, Traversable)

data Chk a
    = Syn (Syn a)
    | Lam (ScopeH () Chk Syn a)
  deriving (Functor, Foldable, Traversable)

instance Applicative Syn where
    pure  = return
    (<*>) = ap

instance Monad Syn where
    return = Var

    Var x   >>= k = k x
    App f x >>= k = App (f >>= k) (x >>== k)
    Ann x t >>= k = Ann (x >>== k) t

instance Module Chk Syn where
    Syn x >>== k = Syn (x >>= k)
    Lam e >>== k = Lam (e >>== k)

instance IsString a => IsString (Syn a) where fromString = Var . fromString
instance IsString a => IsString (Chk a) where fromString = Syn . fromString

instance Show1 Syn where
    liftShowsPrec sp _  d (Var x)   = showsUnaryWith sp "Var" d x
    liftShowsPrec sp sl d (App f x) = showsBinaryWith (liftShowsPrec sp sl) (liftShowsPrec sp sl) "App" d f x
    liftShowsPrec sp sl d (Ann x t) = showsBinaryWith (liftShowsPrec sp sl) showsPrec "Ann" d x t

instance Show1 Chk where
    liftShowsPrec sp sl d (Syn e) = showsUnaryWith (liftShowsPrec sp sl) "Syn" d e
    liftShowsPrec sp sl d (Lam e) = showsUnaryWith (liftShowsPrec sp sl) "Lam" d e

instance Show a => Show (Syn a) where showsPrec = showsPrec1

lam :: Eq a => a -> Chk a -> Chk a
lam x e = Lam (abstract1H x e)

-------------------------------------------------------------------------------
-- Typechecker
-------------------------------------------------------------------------------

-- | >>> typeCheck (const Nothing) (Ann (lam "x" "x") ("Int" :-> "Int") :: Syn String)
-- Just (Ty "Int" :-> Ty "Int")
--
typeCheck :: (a -> Maybe Ty) -> Syn a -> Maybe Ty
typeCheck ctx e = do
    et <- traverse ctx e
    type_ et
  where
    type_ :: Syn Ty -> Maybe Ty 
    type_ (Var ty) = Just ty
    type_ (App f x) = do
        ft <- type_ f
        case ft of
            a :-> b -> do
                check_ x a
                return b
            _ -> Nothing
    type_ (Ann x t) = do
        check_ x t
        return t

    check_ :: Chk Ty -> Ty -> Maybe ()
    check_ (Syn x) t = do
        t' <- type_ x
        guard (t == t')

    check_ (Lam x) (a :-> b) =
        check_ (instantiate1H (Var a) x) b

    check_ (Lam _) _ = Nothing

-------------------------------------------------------------------------------
-- To STLC
-------------------------------------------------------------------------------

-- | Convert to unidirectional STLC.
--
-- >>> Just (ty, uni) = toSTLC (const Nothing) (Ann (lam "x" "x") ("Int" :-> "Int") :: Syn String)
-- >>> ty
-- Ty "Int" :-> Ty "Int"
--
-- >>> uni
-- Lam (Ty "Int") (Scope (Var (B ())))
--
-- >>> Uni.typeCheck (const Nothing) uni
-- Just (Ty "Int" :-> Ty "Int")
--
toSTLC :: (a -> Maybe Ty) -> Syn a -> Maybe (Ty, Uni.Expr a)
toSTLC = type_
  where
    type_ :: (a -> Maybe Ty) -> Syn a -> Maybe (Ty, Uni.Expr a)
    type_ ctx (Var x) = do
        ty <- ctx x
        return (ty, Uni.Var x)

    type_ ctx (App f x) = do
        (ft, f') <- type_ ctx f
        case ft of
            a :-> b -> do
                x' <- check_ ctx x a
                return (b, Uni.App f' x')
            _ -> Nothing

    type_ ctx (Ann x t) = do
        x' <- check_ ctx x t
        return (t, x')

    check_ :: (a -> Maybe Ty) -> Chk a -> Ty -> Maybe (Uni.Expr a)
    check_ ctx (Syn x) ty = do
        (xt, t') <- type_ ctx x
        guard (xt == ty)
        return t'

    check_ ctx (Lam x) (a :-> b) = do
        x' <- check_ (addContext a ctx) (fromScopeH x) b
        return (Uni.Lam a (toScope x'))

    check_ _ (Lam _) _ = Nothing

addContext :: Ty -> (a -> Maybe Ty) -> Var () a -> Maybe Ty
addContext ty ctx = unvar (const (Just ty)) ctx

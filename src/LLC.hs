{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
module LLC where

import Bound
import Bound.Var (unvar)
import Control.Monad (ap, guard)
import Data.Functor.Classes
import Data.String (IsString (..))
import Control.Monad.Trans.State

-------------------------------------------------------------------------------
-- Ty
-------------------------------------------------------------------------------

data Ty
    = Ty String
    | Ty :-> Ty -- imagine this is a lollipop: -o
  deriving (Eq, Ord, Show)

infixr 1 :->

instance IsString Ty where fromString = Ty

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

{-
-------------------------------------------------------------------------------
-- IxStateT
-------------------------------------------------------------------------------

newtype IxStateT m i o a = IxStateT { runIxStateT :: i -> m (o, a) }

ireturn :: Monad m => a -> IxStateT m i i a
ireturn x = IxStateT $ \i -> return (i, x)

(>>-) :: Monad m => IxStateT m i j a -> (a -> IxStateT m j k b) -> IxStateT m i k b
m >>- k = IxStateT $ \i -> do
    (j, a) <- runIxStateT m i
    runIxStateT (k a) j
-}

-------------------------------------------------------------------------------
-- Type-checker
-------------------------------------------------------------------------------

-- |
--
-- >>> let tc e = typeCheck (const Nothing) e
--
-- >>> tc (lam "x" "Int" "x" :: Expr String)
-- Just (Ty "Int" :-> Ty "Int")
--
-- >>> tc (lam "x" "A" $ lam "y" "B" "x" :: Expr String)
-- Nothing
--
-- >>> tc (lam "f" ("A" :-> "A") $ lam "x" "A" $ App "f" "x" :: Expr String)
-- Just ((Ty "A" :-> Ty "A") :-> (Ty "A" :-> Ty "A"))
--
-- >>> tc (lam "f" ("A" :-> "A") $ lam "x" "A" $ App "f" (App "f" "x") :: Expr String)
-- Nothing
--
typeCheck :: Eq a => (a -> Maybe Ty) -> Expr a -> Maybe Ty
typeCheck ctx expr = evalStateT (go expr)  ctx

go :: forall a. Eq a => Expr a -> StateT (a -> Maybe Ty) Maybe Ty
go (Var x) = do
    ctx <- get
    case ctx x of
        Nothing -> fail "unbound variable"
        Just ty -> do
            put (\y -> if x == y then Nothing else ctx y)
            return ty

go (App f x) = do
    ft <- go f
    case ft of
        a :-> b -> do
            xt <- go x
            guard (a == xt)
            return b
        _ -> fail "Function type expected"

go (Lam a x) =
    let x' :: Expr (Var () a)
        x' = fromScope x

    in StateT $ \ctx0 -> do
        let ctx1 :: Var () a -> Maybe Ty
            ctx1 = unvar (const (Just a)) ctx0

        (b, ctx2) <- runStateT (go x') ctx1

        case ctx2 (B ()) of
            Nothing -> do
                let ctx3 :: a -> Maybe Ty
                    ctx3 = ctx2 . F

                return (a :-> b, ctx3)

            Just _ -> fail "non consumed"
        

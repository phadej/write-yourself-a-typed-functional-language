{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
module LambdaPi where

import Bound.Class
import Bound.Scope
import Bound.ScopeH
import Bound.Var
import Control.Monad (ap, guard)
import Control.Monad.Module
import Control.Monad.Trans.Class (lift)
import Data.Bifoldable (Bifoldable (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Bitraversable (Bitraversable (..), bimapDefault, bifoldMapDefault)
import Data.Functor.Classes
import Data.String (IsString (..))
import Data.Void (Void, absurd)

import qualified Bound.Scope.Simple as S

data Syn a
    = Var a
    | Type
    | Pi (Syn a) (Scope () Syn a)
    | App (Syn a) (Chk a)
    | Ann (Chk a) (Syn a)
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

    Type    >>= _ = Type
    Pi x e  >>= k = Pi (x >>= k) (e >>>= k)
    Var x   >>= k = k x
    App f x >>= k = App (f >>= k) (x >>== k)
    Ann x t >>= k = Ann (x >>== k) (t >>= k)

instance Module Chk Syn where
    Syn x >>== k = Syn (x >>= k)
    Lam e >>== k = Lam (e >>== k)

instance IsString a => IsString (Syn a) where fromString = Var . fromString
instance IsString a => IsString (Chk a) where fromString = Syn . fromString

instance Show1 Syn where
    liftShowsPrec _ _   _ Type      = showString "Type"
    liftShowsPrec sp sl d (Pi x t)  = showsBinaryWith (liftShowsPrec sp sl) (liftShowsPrec sp sl) "Pi" d x t
    liftShowsPrec sp _  d (Var x)   = showsUnaryWith sp "Var" d x
    liftShowsPrec sp sl d (App f x) = showsBinaryWith (liftShowsPrec sp sl) (liftShowsPrec sp sl) "App" d f x
    liftShowsPrec sp sl d (Ann x t) = showsBinaryWith (liftShowsPrec sp sl) (liftShowsPrec sp sl) "Ann" d x t

instance Show1 Chk where
    liftShowsPrec sp sl d (Syn e) = showsUnaryWith (liftShowsPrec sp sl) "Syn" d e
    liftShowsPrec sp sl d (Lam e) = showsUnaryWith (liftShowsPrec sp sl) "Lam" d e

instance Show a => Show (Syn a) where showsPrec = showsPrec1

lam :: Eq a => a -> Chk a -> Chk a
lam x e = Lam (abstract1H x e)

(~>) :: Syn a -> Syn a -> Syn a
a ~> b = Pi a (lift b)

-------------------------------------------------------------------------------
-- Value
-------------------------------------------------------------------------------

type Value = Intro Void

data Intro err a
    = VLam (S.Scope () (Intro err) a)
    | VCoerce (Elim err a)
    | VType
    | VPi (Intro err a) (S.Scope () (Intro err) a)
    | VErr err
  deriving (Functor)

data Elim err a
    = Val a
    | VApp (Elim err a) (Intro err a) 
  deriving (Functor)

instance IsString err => Applicative (Intro err) where
    pure = return
    (<*>) = ap

instance IsString err => Applicative (Elim err) where
    pure = return
    (<*>) = ap

instance IsString err => Monad (Intro err) where
    VType     >>= _  = VType
    VCoerce x >>= k = introBind x k
    VLam x    >>= k = VLam (x >>>= k)
    VErr err  >>= _ = VErr err
    VPi x t   >>= k = VPi (x >>= k) (t >>>= k)

instance IsString err => Monad (Elim err) where
    Val x    >>= k = k x
    VApp f x >>= k = VApp (f >>= k) (x >>== k)

instance Bifunctor  Intro where bimap = bimapDefault
instance Bifunctor  Elim  where bimap = bimapDefault
instance Bifoldable Intro where bifoldMap = bifoldMapDefault
instance Bifoldable Elim  where bifoldMap = bifoldMapDefault

instance Bitraversable Intro where
    bitraverse f g (VLam x)    = VLam <$> S.bitraverseScope f g x
    bitraverse f g (VCoerce x) = VCoerce <$> bitraverse f g x
    bitraverse _ _ VType       = pure VType
    bitraverse f g (VPi x b)   = VPi <$> bitraverse f g x <*> S.bitraverseScope f g b
    bitraverse f _ (VErr err)  = VErr <$> f err

instance Bitraversable Elim where
    bitraverse _ g (Val x)    = Val <$> g x
    bitraverse f g (VApp h x) = VApp <$> bitraverse f g h <*> bitraverse f g x

instance IsString err => Module (Intro err) (Elim err) where
    v >>== k = v >>= VCoerce . k 

introBind :: IsString err => Elim err a -> (a -> Intro err b) -> Intro err b
introBind (Val x) k = k x
introBind (VApp f x) k = case introBind f k of
    VCoerce f' -> VCoerce (VApp f' (x >>= k))
    VLam f'    -> S.instantiate1 (x >>= k) f'
    VErr err   -> VErr err
    _          -> VErr (fromString "Invalid application")

instance Show err => Show1 (Intro err) where
    liftShowsPrec _  _  _ VType       = showString "VType"
    liftShowsPrec sp sl d (VCoerce x) = showsUnaryWith (liftShowsPrec sp sl) "VCoerce" d x
    liftShowsPrec sp sl d (VPi x t)   = showsBinaryWith (liftShowsPrec sp sl) (liftShowsPrec sp sl) "VPi" d x t
    liftShowsPrec _  _  d (VErr err)  = showsPrec d err
    liftShowsPrec sp sl d (VLam x)    = showsUnaryWith (liftShowsPrec sp sl) "VLam" d x

instance Show err => Show1 (Elim err) where
    liftShowsPrec sp _  d (Val a)    = showsUnaryWith sp "Val" d a
    liftShowsPrec sp sl d (VApp f x) = showsBinaryWith (liftShowsPrec sp sl) (liftShowsPrec sp sl) "VApp" d f x

instance (Show err, Show a) => Show (Intro err a) where showsPrec = showsPrec1

instance Eq1 (Intro err) where
    liftEq _  VType       VType        = True
    liftEq eq (VCoerce a) (VCoerce a') = liftEq eq a a'
    liftEq eq (VLam a)    (VLam a')    = liftEq eq a a'
    liftEq eq (VPi a b)   (VPi a' b')  = liftEq eq a a' && liftEq eq b b'

    -- err is inequal with everything
    liftEq _ VErr {} _ = False

    liftEq _ VType {}   _ = False
    liftEq _ VCoerce {} _ = False
    liftEq _ VLam {}    _ = False
    liftEq _ VPi {}     _ = False

instance Eq1 (Elim err) where
    liftEq eq (Val a) (Val a') = eq a a'
    liftEq eq (VApp a b) (VApp a' b') =
        liftEq eq a a' && liftEq eq b b'

    liftEq _ Val {}  _ = False
    liftEq _ VApp {} _ = False

instance Eq a => Eq (Intro err a) where (==) = eq1

-------------------------------------------------------------------------------
-- Eval
-------------------------------------------------------------------------------

evalSyn :: IsString err => Syn a -> Intro err a
evalSyn (Var x)   = VCoerce (Val x)
evalSyn Type      = VType
evalSyn (Pi x t)  = VPi (evalSyn x) (S.toScope $ evalSyn $ fromScope t)
evalSyn (Ann x _) = evalChk x
evalSyn (App f x) = do
    b <- VCoerce (VApp (Val True) (VCoerce (Val False)))
    if b then evalSyn f else evalChk x

evalChk :: IsString err => Chk a -> Intro err a
evalChk (Syn x) = evalSyn x
evalChk (Lam b) = VLam (S.toScope $ evalChk $ fromScopeH b)

-------------------------------------------------------------------------------
-- Typechecker
-------------------------------------------------------------------------------

-- |
--
-- >>> let intToInt = "Int" ~> "Int" :: Syn String
-- >>> intToInt
-- Pi (Var "Int") (Scope (Var (F (Var "Int"))))
--
-- >>> evalSyn intToInt
-- VPi (VCoerce (Val "Int")) (Scope (VCoerce (Val (F "Int"))))
--
-- >>> typeCheck (const (Just VType)) (Ann (lam "x" "x") ("Int" ~> "Int") :: Syn String)
-- Just (VPi (VCoerce (Val "Int")) (Scope (VCoerce (Val (F "Int")))))
--
typeCheck :: Eq a => (a -> Maybe (Value a)) -> Syn a -> Maybe (Value a)
typeCheck ctx0 expr = do
    ty <- type_ (fmap (first absurd) . ctx0) expr
    errorless_ ty
  where
    type_ :: Eq a => (a -> Maybe (Intro String a)) -> Syn a -> Maybe (Intro String a)
    type_ ctx (Var ty) = ctx ty
    type_ _ Type       = return VType
    type_ ctx (Ann x t) = do
        tt <- type_ ctx t
        guard (tt == VType)
        let t' = evalSyn t
        check_ ctx x t'
        return t'
    type_ ctx (Pi a b) = do
        a' <- type_ ctx a
        guard (a' == VType)
        b' <- type_ (addContext (evalSyn a) ctx) (fromScope b)
        guard (b' == VType)
        return VType
    type_ ctx (App f x) = do
        f' <- type_ ctx f
        case f' of
            VPi a b -> do
                check_ ctx x a
                return (S.instantiate1 (evalChk x) b)
            _       -> Nothing

    check_ :: Eq a => (a -> Maybe (Intro String a)) -> Chk a -> Intro String a -> Maybe ()
    check_ ctx (Syn x) ty = do
        t <- type_ ctx x
        guard  (t == ty)

    check_ ctx (Lam e) (VPi x t) = do
        let e' = fromScopeH e
        let t' = S.fromScope t
        check_ (addContext x ctx) e' t'

    check_ _ Lam {} _ = Nothing

errorless_ :: Intro String b -> Maybe (Value b)
errorless_ = bitraverse (const Nothing) pure

addContext
    :: Intro String a
    -> (a -> Maybe (Intro String a))
    -> Var () a
    -> Maybe (Intro String (Var () a))
addContext x _ (B ()) = Just (fmap F x)
addContext _ f (F x)  = fmap F <$> f x

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedRecordUpdate #-}
{-# LANGUAGE RecordWildCards#-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UndecidableInstances #-} -- For MonadError
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Main where

import Prelude hiding (lookup)

import Data.Text (Text)
import Data.Fix (Fix(..), foldFix, foldFixM)
import Data.String (IsString(..))
import Data.Word (Word64)
import Data.Functor.Identity (Identity(..))
import Data.Bifunctor (Bifunctor(..))
import Data.Map (Map, fromList, union, singleton, lookup)
import Data.Maybe (maybe, fromMaybe)
import Control.Monad (zipWithM, void)
import Control.Monad.State.Strict (StateT, MonadState(..), runStateT)
import Control.Monad.Except (ExceptT, MonadError(..), runExceptT)
import Control.Monad.Trans (MonadTrans(..))
import System.Random (StdGen, genWord64, getStdGen)
import Data.Bifoldable (Bifoldable(..))
import Data.Bitraversable (Bitraversable(..), bimapDefault, bifoldMapDefault)

newtype OccName = OccName { unOccName :: Text }
  deriving newtype (IsString, Eq, Ord, Show)

data Unique = Unique Word64 Word64
  deriving stock (Eq, Ord, Show)

newtype FreshT m a = FreshT { unFreshT :: StateT StdGen m a }
  deriving newtype (Functor, Applicative, Monad, MonadTrans)

runFreshT :: Functor m => StdGen -> FreshT m a -> m a
runFreshT g (FreshT s) = fst <$> (runStateT s g)

runFresh :: StdGen -> Fresh a -> a
runFresh = fmap runIdentity . runFreshT

data Err =
  NameNotInScope OccName
  deriving (Eq, Ord, Show)

newtype SimplifyT m a = SimplifyT { unSimplifyT :: FreshT (ExceptT Err m) a }
  deriving newtype (Functor, Applicative, Monad, MonadFresh, MonadError Err)

type Simplify = SimplifyT Identity

runSimplifyT :: Functor m => StdGen -> SimplifyT m a -> m (Either Err a)
runSimplifyT g (SimplifyT f) = runExceptT $ runFreshT g f

runSimplify :: StdGen -> Simplify a -> Either Err a
runSimplify = fmap runIdentity . runSimplifyT

class Monad m => MonadFresh m where
  fresh :: m Unique

freshName :: MonadFresh m => OccName -> m Name
freshName occ = Name occ <$> fresh

instance Monad m => MonadFresh (FreshT m) where
  fresh = FreshT $ do
    gen <- get
    let (x, gen') = genWord64 gen
        (y, gen'') = genWord64 gen'
    put gen''
    pure $ Unique x y

instance MonadError e m => MonadError e (FreshT m) where
  throwError = lift . throwError
  catchError x h = FreshT $ catchError (unFreshT x) (unFreshT . h)

class (MonadFresh m, MonadError Err m) => MonadIlluminate m where
  illuminate :: OccEnv -> OccSimpleExpression -> m SimpleExpression
  illuminate occEnv = go occEnv
    where
      go :: MonadIlluminate m => OccEnv -> OccSimpleExpression -> m SimpleExpression
      go env = \case
        EVar n -> EVar <$> lookupOrErr env n
        ECons n -> ECons <$> lookupOrErr env n
        ELam ns e -> do
          newNames <- traverse (\n -> traverse freshName (n, n)) ns
          let newEnv = fromList newNames `union` env
          ELam (snd <$> newNames) <$> (go newEnv e)
        ECase e ps -> do
          newPs <- traverse (goPat env) (fst <$> ps)
          ECase <$> (go env e) <*> zipWithM (\(p', env') e' -> (p',) <$> go env' e') newPs (snd <$> ps)
        ELet bs e -> do
          newNames <- traverse (\(n, _) -> traverse freshName (n, n)) bs
          let newEnv = fromList newNames `union` env
          ELet <$> (traverse (bitraverse freshName (go newEnv)) bs) <*> (go newEnv e)
        ELit l -> pure (ELit l)
        EApp e es -> EApp <$> (go env e) <*> (traverse (go env) es)
        EOp o -> EOp <$> goOp env o

      goPat :: MonadIlluminate m => OccEnv -> OccSimplePattern -> m (SimplePattern, OccEnv)
      goPat env = \case
        PLit l -> pure (PLit l, env)
        PVar n -> do
          newName <- freshName n
          let newNames = singleton n newName
              newEnv = newNames `union` env
          pure (PVar newName, newEnv)
        PCons n ps -> do
          newNames <- traverse (\n -> traverse freshName (n, n)) ps
          let newEnv = fromList newNames `union` env
          (, newEnv) <$> (PCons <$> (lookupOrErr env n) <*> pure (snd <$> newNames))

      goOp :: MonadIlluminate m => OccEnv -> Op OccName OccSimplePattern -> m (Op Name SimplePattern)
      goOp env = \case
        INeg e -> INeg <$> go env e
        IAdd e1 e2 -> IAdd <$> (go env e1) <*> (go env e2)
        ISub e1 e2 -> ISub <$> (go env e1) <*> (go env e2)
        IMul e1 e2 -> IMul <$> (go env e1) <*> (go env e2)
        IDiv e1 e2 -> IDiv <$> (go env e1) <*> (go env e2)

      lookupOrErr env n = fromMaybe (throwError (NameNotInScope n)) (pure <$> lookup n env)

instance Monad m => MonadIlluminate (SimplifyT m)

type Fresh = FreshT Identity

eclipse :: Expr Name SimplePattern -> Expr OccName OccSimplePattern
eclipse = bimap occ (bimap occ occ)

data Name = Name
  { occ :: OccName
  , uniq :: Unique
  } deriving stock (Eq, Ord, Show)

data Literal = LInt Int
  deriving stock (Eq, Ord, Show)

data Expr name pat =
    EVar name
  | ECons name
  | ELam [name] (Expr name pat)
  | ECase (Expr name pat) [(pat, Expr name pat)]
  | ELet [(name, Expr name pat)] (Expr name pat)
  | ELit Literal
  | EApp (Expr name pat) [Expr name pat]
  | EOp (Op name pat)
  deriving stock (Eq, Ord, Show)

instance Bifunctor Expr where
  bimap = bimapDefault

instance Bifoldable Expr where
  bifoldMap = bifoldMapDefault

instance Bitraversable Expr where
  bitraverse f g = \case
    ELit l -> ELit <$> pure l
    EVar n -> EVar <$> f n
    ECons n -> ECons <$> f n
    ELam ns e -> ELam <$> (traverse f ns) <*> (bitraverse f g e)
    EApp e es -> EApp <$> (bitraverse f g e) <*> (traverse (bitraverse f g) es)
    ELet bs e -> ELet <$> (traverse (bitraverse f (bitraverse f g)) bs) <*> (bitraverse f g e)
    ECase e cs -> ECase <$> (bitraverse f g e) <*> (traverse (bitraverse g (bitraverse f g))) cs
    EOp o -> EOp <$> bitraverse f g o

data Op name pat =
  -- integer ops
    INeg (Expr name pat)  -- ^ Unary negation
  | IAdd (Expr name pat) (Expr name pat)
  | ISub (Expr name pat) (Expr name pat)
  | IMul (Expr name pat) (Expr name pat)
  | IDiv (Expr name pat) (Expr name pat)
  deriving stock (Eq, Ord, Show)

instance Bifunctor Op where
  bimap = bimapDefault

instance Bifoldable Op where
  bifoldMap = bifoldMapDefault

instance Bitraversable Op where
  bitraverse f g = \case
    INeg e -> INeg <$> go e
    IAdd e1 e2 -> go2 IAdd e1 e2
    ISub e1 e2 -> go2 ISub e1 e2
    IMul e1 e2 -> go2 IMul e1 e2
    IDiv e1 e2 -> go2 IDiv e1 e2
    where
      go = bitraverse f g
      go2 c e1 e2 = c <$> go e1 <*> go e2

data Pattern name pat =
    PLit Literal
  | PVar name
  | PCons name [pat]
  deriving stock (Eq, Ord, Show)

instance Functor (Pattern name) where
  fmap = bimap id

instance Foldable (Pattern name) where
  foldMap = bifoldMap (const mempty)

instance Traversable (Pattern name) where
  traverse = bitraverse pure

instance Bifunctor Pattern where
  bimap = bimapDefault

instance Bifoldable Pattern where
  bifoldMap = bifoldMapDefault

instance Bitraversable Pattern where
  bitraverse f g = \case
    PLit l -> PLit <$> pure l
    PVar n -> PVar <$> f n
    PCons n ps -> PCons <$> f n <*> traverse g ps

type SimplePat name = Pattern name name
type SimplePattern = SimplePat Name
type OccSimplePattern = SimplePat OccName

type OccExpression = Expr OccName (Pattern OccName (Fix (Pattern OccName)))
type OccSimpleExpression = Expr OccName OccSimplePattern
type SimpleExpression = Expr Name SimplePattern

type OccEnv = Map OccName Name

testy :: OccExpression
testy = ECase (EApp (ECons "Rawr") [EApp (ECons "Tiger") [ELit (LInt 3), ELit (LInt 5)], ELit (LInt 7)])
              [ (PCons "Rawr" [Fix (PCons "Tiger" [Fix (PLit (LInt 3)), Fix (PLit (LInt 5))]), Fix (PVar "y")], EVar "y")
              , (PVar "_", ELit (LInt 314))
              ]

retesty :: SimpleExpression
retesty = ECase (EApp (ECons (named "Rawr")) [EApp (ECons (named "Tiger")) [ELit (LInt 3), ELit (LInt 5)], ELit (LInt 7)])
                [ (PCons (named "Rawr") [named "$rawr0", named "y"],
                   ECase (EVar (named "$rawr0"))
                         [ (PCons (named "Tiger") [named "$tiger0", named "$tiger1"],
                            ECase (EVar (named "$tiger0"))
                                  [ (PLit (LInt 3),
                                     ECase (EVar (named "$tiger1"))
                                           [ (PLit (LInt 5), EVar (named "y"))
                                           , (PVar (named "$_"), ELit (LInt 314))
                                           ])
                                  , (PVar (named "$_"), ELit (LInt 314))
                                  ])
                         , (PVar (named "$_"), ELit (LInt 314))
                         ])
                , (PVar (named "_"), ELit (LInt 314))
                ]
  where
    u0 = Unique 0 0
    named x = Name x u0

foldPatternM :: Monad m => (Pattern name a -> m a) -> Pattern name (Fix (Pattern name)) -> m (Pattern name a)
foldPatternM f = \case
  PLit l -> PLit <$> pure l
  PVar n -> PVar <$> pure n
  PCons n ps -> PCons n <$> (traverse (foldFixM f) ps)

emptyOccEnv :: OccEnv
emptyOccEnv = mempty

main :: IO ()
main = do
  g <- getStdGen
  void
    $ bitraverse print (print . eclipse)
    $ runSimplify g
    $ illuminate emptyOccEnv
    $ ELam ["fuck", "me"] (ELam ["me"] (EVar "tits"))

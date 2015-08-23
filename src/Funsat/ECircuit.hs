{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | Boolean circuits with more expressive language.
--  * Extended propositional circuits
--  * Circuits with order constraints
--  * Circuits with quantification

module Funsat.ECircuit
    (
    -- ** Circuit type class
      Circuit(..), Co
    , ECircuit(..)
    , NatCircuit(..), sum, Natural(..), MaxCircuit(..)
    , ExistCircuit(..), existsN
    , ForallCircuit(..)
    , CastCircuit(..)
    -- ** Circuit evaluator
    , BEnv, BIEnv
    , Eval, EvalF(..), runEval
    )
where

{-
    This file is part of funsat.

    funsat is free software: you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    funsat is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with funsat.  If not, see <http://www.gnu.org/licenses/>.

    Copyright 2008 Denis Bueno
-}
import Control.DeepSeq (NFData)
import Control.Monad.Cont
import Data.Ord()
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Funsat.Circuit (Circuit(..), CastCircuit(..), Co
                      ,EvalF(..), Eval
                      ,BEnv, BIEnv)
import Prelude hiding( not, and, or, fromInteger, negate, sum, max )
import qualified Data.Map as Map
import qualified Prelude  as P

-- * Circuit representation

-- | A class representing a grammar for logical circuits.  Default
-- implemenations are indicated.
class Circuit repr => ECircuit repr where
    -- | If-then-else circuit.  @ite c t e@ returns a circuit that evaluates to
    -- @t@ when @c@ evaluates to true, and @e@ otherwise.
    --
    -- Defined as @(c `and` t) `or` (not c `and` f)@.
    ite :: (Co repr var) => repr var -> repr var -> repr var -> repr var
    ite c t f = (c `and` t) `or` (not c `and` f)

    -- | Defined as @`onlyif' p q = not p `or` q@.
    onlyif :: (Co repr var) => repr var -> repr var -> repr var
    onlyif p q = not p `or` q

    -- | Defined as @`iff' p q = (p `onlyif` q) `and` (q `onlyif` p)@.
    iff :: (Co repr var) => repr var -> repr var -> repr var
    iff p q = (p `onlyif` q) `and` (q `onlyif` p)

    -- | Defined as @`xor' p q = (p `or` q) `and` not (p `and` q)@.
    xor :: (Co repr var) => repr var -> repr var -> repr var
    xor p q = (p `or` q) `and` not (p `and` q)

-- | A class for circuits with existential quantification
class Circuit repr => ExistCircuit repr where
    existsBool :: Co repr var => (repr var -> repr var) -> repr var
    existsNat  :: Co repr var => (repr var -> repr var) -> repr var

-- Type for natural variables
newtype Natural v = Natural {encodeNatural::v} deriving (Eq,Ord,Show,Functor,Foldable,Traversable,NFData)

-- | A class for circuits with order constraints
class Circuit repr => NatCircuit repr where
    -- | Ordering constraints for binary represented (lsb first) naturals
    gt,ge,lt,le,eq :: Co repr var => repr var -> repr var -> repr var
    nat      :: Co repr var => Natural var -> repr var
    iteNat   :: Co repr var => repr var -> repr var -> repr var -> repr var
    (+#)     :: Co repr var => repr var -> repr var -> repr var
    (-#)     :: Co repr var => repr var -> repr var -> repr var
    (*#)     :: Co repr var => repr var -> repr var -> repr var
    negate   :: Co repr var => repr var -> repr var
    fromInteger :: Co repr var => Integer -> repr var
    negate x = fromInteger 0 -# x
    gt x y   = not (le x y)
    ge x y   = not (lt x y)
    le x y   = (lt x y `or` eq x y)
    a -# b   = a +# negate b

class NatCircuit repr => MaxCircuit repr where
  maxL :: [repr var] -> repr var
  max  :: repr var -> repr var -> repr var

  maxL = foldr1 max
  max a b = maxL [a,b]

sum :: (Co repr var, NatCircuit repr) => [repr var] -> repr var
sum xx = foldr (+#) (fromInteger 0) xx

existsN :: (ExistCircuit repr, Co repr var) => Int -> ([repr var] -> repr var) -> repr var
existsN n k = (`runCont` id) $ do {xx <- replicateM n (cont existsBool); return $ k xx}

-- | A class for circuits with universal quantification
class ExistCircuit repr => ForallCircuit repr where
    forall :: Co repr var => (repr var -> repr var) -> repr var

-- ** Circuit evaluator

-- | Evaluate a circuit given inputs.
runEval :: BIEnv v -> Eval v -> Either Int Bool
runEval = flip unEval

liftEvalBool2 op c1 c2 = Eval (\env -> Right $ fromLeft(unEval c1 env) `op` fromLeft(unEval c2 env))
liftEvalInt2 op c1 c2 = Eval (\env -> Left $ fromLeft(unEval c1 env) `op` fromLeft(unEval c2 env))

instance NatCircuit Eval where
    eq   = liftEvalBool2 (==)
    lt   = liftEvalBool2 (<)
    (+#) = liftEvalInt2 (+)
    (-#) = liftEvalInt2 (-)
    (*#) = liftEvalInt2 (*)
    fromInteger i = Eval(\_ -> Left (P.fromInteger i))
    nat v       = Eval (\env -> Map.findWithDefault (Left (0 :: Int))
--                                     (error $ "Eval: no such nat: " ++ show v
  --                                         ++ " in " ++ show env)
                                     (encodeNatural v) env)
    iteNat cond then_ else_ = Eval $ \env ->
      case (unEval cond env) of
        Right True  -> unEval then_ env
        Right False -> unEval else_ env

instance ECircuit Eval

instance MaxCircuit Eval where
  max = liftEvalInt2 P.max

fromLeft  :: Either Int Bool -> Int
fromLeft  =   either  id  (typeError "runEval: Expected a natural.")

typeError :: String -> a
typeError msg = error (msg ++ "\nPlease send an email to the pepeiborra@gmail.com requesting a typed circuit language.")

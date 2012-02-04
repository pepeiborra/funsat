{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}

-- | Boolean circuits with more expressive language.
--  * Extended propositional circuits
--  * Circuits with order constraints
--  * Circuits with quantification

module Funsat.ECircuit
    (
    -- ** Circuit type class
      Circuit(..)
    , ECircuit(..)
    , NatCircuit(..)
    , ExistCircuit(..), ForallCircuit(..)
    , CastCircuit(..)

    -- ** bit-encoded Naturals
    , fromBinary

    -- ** Explicit sharing circuit
    , Shared(..)
    , FrozenShared(..)
    , runShared
    , CircuitHash
    , falseHash
    , trueHash
    , CCode(..)
    , CMaps(..)
    , emptyCMaps

    -- ** Explicit tree circuit
    , Tree(..)
    , foldTree

    -- *** Circuit simplification
    , simplifyTree, removeComplex, removeNats
#ifdef TESTING
    , removeNats'
#endif

    -- ** Explicit graph circuit
    , Graph
    , runGraph
    , shareGraph, shareGraph'
    , NodeType(..)
    , EdgeType(..)

    -- ** Circuit evaluator
    , BEnv, BIEnv
    , Eval, EvalF(..)
    , runEval

    -- ** Convert circuit to CNF
    , ECircuitProblem(..), CNF(..)
    , toCNF
    , projectECircuitSolution
    , reconstructNatsFromBits
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

import Control.Applicative
import Control.Arrow (first, second)
import Control.Exception (assert)
import Control.Monad.Cont
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.State.Strict hiding ((>=>), forM_)
import Data.Bimap( Bimap )
import Data.Foldable (Foldable, foldMap)
import Data.List( nub, sortBy)
import Data.List.Split ( chunk )
import Data.Map( Map )
import Data.Maybe( fromJust )
import Data.Ord()
import Data.Set( Set )
import Data.Traversable (Traversable, traverse, fmapDefault, foldMapDefault)
import Funsat.Types( CNF(..), Lit(..), Var(..), var, lit, Solution(..), litSign, litAssignment )
import Funsat.Circuit (Circuit(..), CastCircuit(..), Co
                      ,EvalF(..), Eval
                      ,BEnv, BIEnv)
import Prelude hiding( not, and, or )

import qualified Data.Bimap as Bimap
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Map as Map
import qualified Data.Set as Set


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

-- | A class for circuits with order constraints
class Circuit repr => NatCircuit repr where
    -- | Ordering constraints for binary represented (lsb first) naturals
    nat   :: (Co repr var) => var -> repr var
    gt,lt,eq :: (Co repr var) => repr var -> repr var -> repr var
    gt x y = not (lt x y) `and` not (eq x y)

-- | A class for circuits with existential quantification
class Circuit repr => ExistCircuit repr where
    exists :: Co repr var => (repr var -> repr var) -> repr var
    existsN :: Co repr var => Int -> ([repr var] -> repr var) -> repr var

    exists k = existsN 1 (\[x] -> k x)
    existsN n k = (`runCont` id) $ do {xx <- replicateM n (cont exists); return $ k xx}

-- | A class for circuits with universal quantification
class ExistCircuit repr => ForallCircuit repr where
    forall :: Co repr var => (repr var -> repr var) -> repr var

-- ** Explicit sharing circuit

-- The following business is for elimination of common subexpressions from
-- boolean functions.  Part of conversion to CNF.

-- | A `Circuit' constructed using common-subexpression elimination.  This is a
-- compact representation that facilitates converting to CNF.  See `runShared'.
newtype Shared v = Shared { unShared :: State (CMaps v) CCode }

-- | A shared circuit that has already been constructed.
data FrozenShared v = FrozenShared !CCode !(CMaps v) deriving (Eq)

instance Show v => Show (FrozenShared v) where
  showsPrec p (FrozenShared c maps) = showString "FrozenShared " . showParen True (showsPrec p c)
                                                                 . showChar ' '
                                                                 . showsPrec p maps{hashCount=[]}

-- | Reify a sharing circuit.
runShared :: Shared v -> FrozenShared v
runShared = uncurry FrozenShared . (`runState` emptyCMaps) . unShared

instance (ECircuit c, NatCircuit c, ExistCircuit c) => CastCircuit Shared c where
    castCircuit = castCircuit . runShared

instance (ECircuit c, NatCircuit c) => CastCircuit FrozenShared c where
    castCircuit (FrozenShared code maps) = go code
      where
        go    CTrue{}    = true
        go    CFalse{}   = false
        go c@(CVar{})    = input $ getChildren c (varMap maps)
--        go    CExist{}   = exists id
        go    CExist{}   = error "cannot cast circuits with existential constraints"
        go c@(CAnd{})    = uncurry and    . go2 $ getChildren c (andMap maps)
        go c@(COr{})     = uncurry or     . go2 $ getChildren c (orMap maps)
        go c@(CNot{})    = not            . go  $ getChildren c (notMap maps)
        go c@(CXor{})    = uncurry xor    . go2 $ getChildren c (xorMap maps)
        go c@(COnlyif{}) = uncurry onlyif . go2 $ getChildren c (onlyifMap maps)
        go c@(CIff{})    = uncurry iff    . go2 $ getChildren c (iffMap maps)
        go c@(CIte{})    = uncurry3 ite   . go3 $ getChildren c (iteMap maps)
        go c@CEq{}       = uncurry eq     . go2 $ getChildren c (eqMap maps)
        go c@CLt{}       = uncurry lt     . go2 $ getChildren c (ltMap maps)
        go c@CNat{}      = nat $ getChildren c (natMap maps)

        go2 = (go `onTup`)
        go3 (x, y, z) = (go x, go y, go z)
        uncurry3 f (x, y, z) = f x y z

getChildren :: (Ord v) => CCode -> Bimap CircuitHash v -> v
getChildren code codeMap =
    case Bimap.lookup (circuitHash code) codeMap of
      Nothing -> findError
      Just c  -> c
  where findError = error $ "getChildren: unknown code: " ++ show code

-- | 0 is false, 1 is true.  Any positive value labels a logical circuit node.
type CircuitHash = Int

falseHash, trueHash :: CircuitHash
falseHash = 0
trueHash  = 1

-- | A `CCode' represents a circuit element for `Shared' circuits.  A `CCode' is
-- a flattened tree node which has been assigned a unique number in the
-- corresponding map inside `CMaps', which indicates children, if any.
--
-- For example, @CAnd i@ has the two children of the tuple @lookup i (andMap
-- cmaps)@ assuming @cmaps :: CMaps v@.
data CCode = CTrue   { circuitHash :: !CircuitHash }
           | CFalse  { circuitHash :: !CircuitHash }
           | CVar    { circuitHash :: !CircuitHash }
           | CExist  { circuitHash :: !CircuitHash }
           | CAnd    { circuitHash :: !CircuitHash }
           | COr     { circuitHash :: !CircuitHash }
           | CNot    { circuitHash :: !CircuitHash }
           | CXor    { circuitHash :: !CircuitHash }
           | COnlyif { circuitHash :: !CircuitHash }
           | CIff    { circuitHash :: !CircuitHash }
           | CIte    { circuitHash :: !CircuitHash }
           | CNat    { circuitHash :: !CircuitHash }
           | CEq     { circuitHash :: !CircuitHash }
           | CLt     { circuitHash :: !CircuitHash }
             deriving (Eq, Ord, Show, Read)

-- | Maps used to implement the common-subexpression sharing implementation of
-- the `Circuit' class.  See `Shared'.
data CMaps v = CMaps
    { hashCount :: ![CircuitHash]
    -- ^ Source of unique IDs used in `Shared' circuit generation.  Should not
    -- include 0 or 1.

    , varMap    :: !(Bimap CircuitHash v)
     -- ^ Mapping of generated integer IDs to variables.

    , existSet  :: !(Set CircuitHash)

    , andMap    :: !(Bimap CircuitHash (CCode, CCode))
    , orMap     :: !(Bimap CircuitHash (CCode, CCode))
    , notMap    :: !(Bimap CircuitHash CCode)
    , xorMap    :: !(Bimap CircuitHash (CCode, CCode))
    , onlyifMap :: !(Bimap CircuitHash (CCode, CCode))
    , iffMap    :: !(Bimap CircuitHash (CCode, CCode))
    , iteMap    :: !(Bimap CircuitHash (CCode, CCode, CCode))
    , natMap    :: !(Bimap CircuitHash v)
    , eqMap     :: !(Bimap CircuitHash (CCode, CCode))
    , ltMap     :: !(Bimap CircuitHash (CCode, CCode))
    }
               deriving (Eq, Show)

-- | A `CMaps' with an initial `hashCount' of 2.
emptyCMaps :: CMaps v
emptyCMaps = CMaps
    { hashCount = [2 ..]
    , varMap    = Bimap.empty
    , existSet  = Set.empty
    , andMap    = Bimap.empty
    , orMap     = Bimap.empty
    , notMap    = Bimap.empty
    , xorMap    = Bimap.empty
    , onlyifMap = Bimap.empty
    , iffMap    = Bimap.empty
    , iteMap    = Bimap.empty
    , natMap    = Bimap.empty
    , eqMap     = Bimap.empty
    , ltMap     = Bimap.empty}

-- | Find key mapping to given value.
lookupv :: Ord v => v -> Bimap Int v -> Maybe Int
lookupv = Bimap.lookupR

-- prj: "projects relevant map out of state"
-- upd: "stores new map back in state"
{-# INLINE recordC #-}
recordC :: (Ord a) =>
           (CircuitHash -> b)
        -> (CMaps v -> Bimap Int a)            -- ^ prj
        -> (CMaps v -> Bimap Int a -> CMaps v) -- ^ upd
        -> a
        -> State (CMaps v) b
recordC _ _ _ x | x `seq` False = undefined
recordC cons prj upd x = do
  s <- get
  c:cs <- gets hashCount
  maybe (do let s' = upd (s{ hashCount = cs })
                         (Bimap.insert c x (prj s))
            put s'
            return (cons c))
        (return . cons) $ lookupv x (prj s)

instance Circuit Shared where
    type Co Shared var = Ord var
    false = Shared falseS
    true  = Shared trueS
    input v = Shared $ recordC CVar varMap (\s e -> s{ varMap = e }) v
    and = liftShared2 andS
    or  = liftShared2 orS
    not = liftShared  notS

instance ECircuit Shared where
    xor = liftShared2 xor_ where
        xor_ CTrue{} c = notS c
        xor_ c CTrue{} = notS c
        xor_ CFalse{} c = return c
        xor_ c CFalse{} = return c
        xor_ hl hr = recordC CXor xorMap (\s e' -> s{ xorMap = e' }) (hl, hr)
    iff = liftShared2 iffS
    onlyif = liftShared2 onlyif_ where
        onlyif_ CFalse{} _ = trueS
        onlyif_ c CFalse{} = notS c
        onlyif_ CTrue{}  c = return c
        onlyif_ _ CTrue{}  = trueS
        onlyif_ hl hr
           | hl == hr  = trueS
           | otherwise = recordC COnlyif onlyifMap (\s e' -> s{ onlyifMap = e' }) (hl, hr)
    ite x t e = Shared $ do
        hx <- unShared x
        ht <- unShared t ; he <- unShared e
        ite_ hx ht he
      where
        ite_ CTrue{} ht _  = return ht
        ite_ CFalse{} _ he = return he
        ite_ b CTrue{}  he = orS b he
        ite_ b CFalse{} he = do {nb <- notS b; andS nb he}
        ite_ b ht CTrue{}  = do {nb <- notS b; orS nb ht}
        ite_ b ht CFalse{} = andS b ht
        ite_ hx ht he = recordC CIte iteMap (\s e' -> s{ iteMap = e' }) (hx, ht, he)

instance ExistCircuit Shared where
    exists k  = Shared $ do
        c:cs <- gets hashCount
        modify $ \s -> s{existSet = Set.insert c (existSet s),hashCount=cs}
        unShared . k . Shared . return . CExist $ c

instance NatCircuit Shared where
    eq sx sy = Shared $ do
      x <- unShared sx
      y <- unShared sy
      if x == y then trueS else recordC CEq eqMap (\s e -> s {eqMap = e}) (x,y)

    lt xx yy = Shared $ do
      x <- unShared xx
      y <- unShared yy
      if x == y then falseS else recordC CLt ltMap (\s e -> s {ltMap = e}) (x,y)

    nat = Shared . recordC CNat natMap (\s e -> s{ natMap = e })

falseS, trueS :: State (CMaps v) CCode
falseS = return $ CFalse falseHash
trueS  = return $ CTrue  trueHash


andS, orS :: CCode -> CCode -> State (CMaps v) CCode
andS c@CFalse{} _ = return c
andS _ c@CFalse{} = return c
andS CTrue{} c  = return c
andS c CTrue{}  = return c
andS hl hr = recordC CAnd andMap (\s e -> s{ andMap = e}) (hl, hr)

notS :: CCode -> State (CMaps v) CCode
notS CTrue{}  = falseS
notS CFalse{} = trueS
notS (CNot i) = do {s <- get; return $ fromJust $ Bimap.lookup i (notMap s) }
notS h        = recordC CNot notMap (\s e' -> s{ notMap = e' }) h

orS c@CTrue{} _ = return c
orS _ c@CTrue{} = return c
orS CFalse{} c  = return c
orS c CFalse{}  = return c
orS hl hr = recordC COr orMap (\s e -> s{ orMap = e }) (hl, hr)

iffS :: CCode -> CCode -> State (CMaps v) CCode
iffS CTrue{} c  = return c
iffS c CTrue{}  = return c
iffS CFalse{} c = notS c
iffS c CFalse{} = notS c
iffS hl hr
 | hl == hr  = trueS
 | otherwise = recordC CIff iffMap (\s e' -> s{ iffMap = e' }) (hl, hr)

{-# INLINE liftShared #-}
liftShared :: (CCode -> State (CMaps v) CCode) -> Shared v -> Shared v
liftShared f a = Shared $ do {h <- unShared a; f h}

{-# INLINE liftShared2 #-}
liftShared2 :: (CCode -> CCode -> State (CMaps v) CCode) -> Shared v -> Shared v -> Shared v
liftShared2 f a b = Shared $ do
  va <- unShared a
  vb <- unShared b
  f va vb

-- ** Explicit tree circuit

-- | Explicit tree representation, which is a generic description of a circuit.
-- This representation enables a conversion operation to any other type of
-- circuit.  Trees evaluate from variable values at the leaves to the root.
data Tree v = TTrue
             | TFalse
             | TLeaf v
             | TNot (Tree v)
             | TAnd (Tree v) (Tree v)
             | TOr  (Tree v) (Tree v)
             | TXor (Tree v) (Tree v)
             | TIff (Tree v) (Tree v)
             | TOnlyIf (Tree v) (Tree v)
             | TIte (Tree v) (Tree v) (Tree v)
             | TEq  (Tree v) (Tree v)
             | TLt  (Tree v) (Tree v)
             | TNat v
               deriving (Show, Eq, Ord)

foldTree :: (t -> v -> t) -> t -> Tree v -> t
foldTree _ i TTrue        = i
foldTree _ i TFalse       = i
foldTree f i (TLeaf v)    = f i v
foldTree f i (TAnd t1 t2) = foldTree f (foldTree f i t1) t2
foldTree f i (TOr t1 t2)  = foldTree f (foldTree f i t1) t2
foldTree f i (TNot t)     = foldTree f i t
foldTree f i (TXor t1 t2) = foldTree f (foldTree f i t1) t2
foldTree f i (TIff t1 t2) = foldTree f (foldTree f i t1) t2
foldTree f i (TOnlyIf t1 t2) = foldTree f (foldTree f i t1) t2
foldTree f i (TIte x t e) = foldTree f (foldTree f (foldTree f i x) t) e
foldTree f i (TEq t1 t2)  = foldTree f (foldTree f i t1) t2
foldTree f i (TLt t1 t2)  = foldTree f (foldTree f i t1) t2
foldTree f i (TNat n)    = f i n

instance Functor Tree where fmap = fmapDefault
instance Foldable Tree where foldMap = foldMapDefault
instance Traversable Tree where
  traverse _ TTrue  = pure TTrue
  traverse _ TFalse = pure TFalse
  traverse f (TLeaf v) = TLeaf <$> f v
  traverse f (TNot t) = TNot <$> traverse f t
  traverse f (TAnd t1 t2) = TAnd <$> traverse f t1 <*> traverse f t2
  traverse f (TOr  t1 t2) = TOr  <$> traverse f t1 <*> traverse f t2
  traverse f (TXor t1 t2) = TXor <$> traverse f t1 <*> traverse f t2
  traverse f (TIff t1 t2) = TIff <$> traverse f t1 <*> traverse f t2
  traverse f (TOnlyIf t1 t2) = TOnlyIf <$> traverse f t1 <*> traverse f t2
  traverse f (TEq t1 t2)  = TEq <$> traverse f t1 <*> traverse f t2
  traverse f (TLt t1 t2)  = TLt <$> traverse f t1 <*> traverse f t2
  traverse f (TIte t1 t2 t3) = TIte <$> traverse f t1 <*> traverse f t2 <*> traverse f t3
  traverse f (TNat v)    = TNat <$> f v

instance Circuit Tree where
    type Co Tree var = ()
    true  = TTrue
    false = TFalse
    input = TLeaf
    and   = TAnd
    or    = TOr
    not   = TNot

instance ECircuit Tree where
    xor   = TXor
    iff   = TIff
    onlyif = TOnlyIf
    ite   = TIte

instance NatCircuit Tree where
    eq    = TEq
    lt    = TLt
    nat   = TNat

instance (ECircuit c, NatCircuit c) => CastCircuit Tree c where
    castCircuit TTrue        = true
    castCircuit TFalse       = false
    castCircuit (TLeaf l)    = input l
    castCircuit (TAnd t1 t2) = and (castCircuit t1) (castCircuit t2)
    castCircuit (TOr t1 t2)  = or (castCircuit t1) (castCircuit t2)
    castCircuit (TXor t1 t2) = xor (castCircuit t1) (castCircuit t2)
    castCircuit (TNot t)     = not (castCircuit t)
    castCircuit (TIff t1 t2) = iff (castCircuit t1) (castCircuit t2)
    castCircuit (TOnlyIf t1 t2) = onlyif (castCircuit t1) (castCircuit t2)
    castCircuit (TIte x t e) = ite (castCircuit x) (castCircuit t) (castCircuit e)
    castCircuit (TEq t1 t2)  = eq (castCircuit t1) (castCircuit t2)
    castCircuit (TLt t1 t2)  = lt (castCircuit t1) (castCircuit t2)
    castCircuit (TNat v)    = nat v

-- ** Circuit evaluator

-- | Evaluate a circuit given inputs.
runEval :: BIEnv v -> Eval v -> Either Int Bool
runEval = flip unEval

instance NatCircuit Eval where
    eq c1 c2  = Eval (\env -> Right $ fromLeft(unEval c1 env) == fromLeft(unEval c2 env))
    lt c1 c2  = Eval (\env -> Right $ fromLeft(unEval c1 env) <  fromLeft(unEval c2 env))
    nat v     = Eval (\env -> Map.findWithDefault
                                     (error $ "Eval: no such nat: " ++ show v
                                           ++ " in " ++ show env)
                                     v env)
instance ECircuit Eval

fromBinary :: Num b => [ Bool ] -> b
fromBinary xs = foldr ( \ x y -> 2*y + if x then 1 else 0 ) 0 xs

fromLeft  :: Either Int Bool -> Int
fromLeft  =   either  id  (typeError "runEval: Expected a natural.")

-- ** Graph circuit

-- | A circuit type that constructs a `G.Graph' representation.  This is useful
-- for visualising circuits, for example using the @graphviz@ package.
newtype Graph v = Graph
    { unGraph :: State Graph.Node (Graph.Node,
                                    [Graph.LNode (NodeType v)],
                                    [Graph.LEdge EdgeType]) }

-- | Node type labels for graphs.
data NodeType v = NInput v
                | NTrue
                | NFalse
                | NAnd
                | NOr
                | NNot
                | NXor
                | NIff
                | NOnlyIf
                | NIte
                | NNat v
                | NEq
                | NLt
                  deriving (Eq, Ord, Show, Read)

data EdgeType = ETest -- ^ the edge is the condition for an `ite' element
              | EThen -- ^ the edge is the /then/ branch for an `ite' element
              | EElse -- ^ the edge is the /else/ branch for an `ite' element
              | EVoid -- ^ no special annotation
                 deriving (Eq, Ord, Show, Read)

runGraph :: (G.DynGraph gr) => Graph v -> gr (NodeType v) EdgeType
runGraph graphBuilder =
    let (_, nodes, edges) = evalState (unGraph graphBuilder) 1
    in Graph.mkGraph nodes edges

instance Circuit Graph where
    type Co Graph var = ()
    input v = Graph $ do
        n <- newNode
        return $ (n, [(n, NInput v)], [])

    true = Graph $ do
        n <- newNode
        return $ (n, [(n, NTrue)], [])

    false = Graph $ do
        n <- newNode
        return $ (n, [(n, NFalse)], [])

    not gs = Graph $ do
        (node, nodes, edges) <- unGraph gs
        n <- newNode
        return (n, (n, NNot) : nodes, (node, n, EVoid) : edges)

    and    = binaryNode NAnd
    or     = binaryNode NOr

instance ECircuit Graph where
    xor    = binaryNode NXor
    iff    = binaryNode NIff
    onlyif = binaryNode NOnlyIf
    ite x t e = Graph $ do
        (xNode, xNodes, xEdges) <- unGraph x
        (tNode, tNodes, tEdges) <- unGraph t
        (eNode, eNodes, eEdges) <- unGraph e
        n <- newNode
        return (n, (n, NIte) : xNodes ++ tNodes ++ eNodes
               , (xNode, n, ETest) : (tNode, n, EThen) : (eNode, n, EElse)
                 : xEdges ++ tEdges ++ eEdges)

instance NatCircuit Graph where
    eq    = binaryNode NEq
    lt    = binaryNode NLt
    nat v = Graph $ do {n <- newNode; return (n, [(n, NNat v)],[])}

binaryNode :: NodeType v -> Graph v -> Graph v -> Graph v
{-# INLINE binaryNode #-}
binaryNode ty l r = Graph $ do
        (lNode, lNodes, lEdges) <- unGraph l
        (rNode, rNodes, rEdges) <- unGraph r
        n <- newNode
        return (n, (n, ty) : lNodes ++ rNodes,
                   (lNode, n, EVoid) : (rNode, n, EVoid) : lEdges ++ rEdges)


newNode :: State Graph.Node Graph.Node
newNode = do i <- get ; put (succ i) ; return i

-- | Given a frozen shared circuit, construct a `G.DynGraph' that exactly
-- represents it.  Useful for debugging constraints generated as `Shared'
-- circuits.
shareGraph :: (G.DynGraph gr, Eq v, Show v) =>
              FrozenShared v -> gr (FrozenShared v) (FrozenShared v)
shareGraph (FrozenShared output cmaps) =
    (`runReader` cmaps) $ do
        (_, nodes, edges) <- go output
        return $ Graph.mkGraph (nub nodes) (nub edges)
  where
    -- Invariant: The returned node is always a member of the returned list of
    -- nodes.  Returns: (node, node-list, edge-list).
    go c@(CVar i) = return (i, [(i, frz c)], [])
    go c@(CExist i) = return (i, [(i, frz c)], [])
    go c@(CTrue i)  = return (i, [(i, frz c)], [])
    go c@(CFalse i) = return (i, [(i, frz c)], [])
    go c@(CNot i) = do
        (child, nodes, edges) <- extract i notMap >>= go
        return (i, (i, frz c) : nodes, (child, i, frz c) : edges)
    go c@(CAnd i) = extract i andMap >>= tupM2 go >>= addKids c
    go c@(COr i) = extract i orMap >>= tupM2 go >>= addKids c
    go c@(CXor i) = extract i xorMap >>= tupM2 go >>= addKids c
    go c@(COnlyif i) = extract i onlyifMap >>= tupM2 go >>= addKids c
    go c@(CIff i) = extract i iffMap >>= tupM2 go >>= addKids c
    go c@(CIte i) = do (x, y, z) <- extract i iteMap
                       ( (cNode, cNodes, cEdges)
                        ,(tNode, tNodes, tEdges)
                        ,(eNode, eNodes, eEdges)) <- liftM3 (,,) (go x) (go y) (go z)
                       return (i, (i, frz c) : cNodes ++ tNodes ++ eNodes
                              ,(cNode, i, frz c)
                               : (tNode, i, frz c)
                               : (eNode, i, frz c)
                               : cEdges ++ tEdges ++ eEdges)

    go c@(CEq i) = extract i eqMap >>= tupM2 go >>= addKids c
    go c@(CLt i) = extract i ltMap >>= tupM2 go >>= addKids c
    go c@(CNat i) = return (i, [(i, frz c)], [])

    addKids ccode ((lNode, lNodes, lEdges), (rNode, rNodes, rEdges)) =
        let i = circuitHash ccode
        in return (i, (i, frz ccode) : lNodes ++ rNodes,
                      (lNode, i, frz ccode) : (rNode, i, frz ccode) : lEdges ++ rEdges)
    tupM2 f (x, y) = liftM2 (,) (f x) (f y)
    frz ccode = FrozenShared ccode cmaps
    extract code f = do
        maps <- ask
        let lookupError = error $ "shareGraph: unknown code: " ++ show code
        case Bimap.lookup code (f maps) of
          Nothing -> lookupError
          Just x  -> return x


shareGraph' :: (G.DynGraph gr, Eq v, Show v) =>
              FrozenShared v -> gr String String
shareGraph' (FrozenShared output cmaps) =
    (`runReader` cmaps) $ do
        (_, nodes, edges) <- go output
        return $ Graph.mkGraph (nub nodes) (nub edges)
  where
    -- Invariant: The returned node is always a member of the returned list of
    -- nodes.  Returns: (node, node-list, edge-list).
    go c@(CVar i) = return (i, [(i, frz c)], [])
    go c@(CExist i) = return (i, [(i, frz c)], [])
    go c@(CTrue i)  = return (i, [(i, frz c)], [])
    go c@(CFalse i) = return (i, [(i, frz c)], [])
    go c@(CNot i) = do
        (child, nodes, edges) <- extract i notMap >>= go
        return (i, (i, frz c) : nodes, (child, i, frz c) : edges)
    go c@(CAnd i) = extract i andMap >>= tupM2 go >>= addKids c
    go c@(COr i) = extract i orMap >>= tupM2 go >>= addKids c
    go c@(CXor i) = extract i xorMap >>= tupM2 go >>= addKids c
    go c@(COnlyif i) = extract i onlyifMap >>= tupM2 go >>= addKids c
    go c@(CIff i) = extract i iffMap >>= tupM2 go >>= addKids c
    go c@(CIte i) = do (x, y, z) <- extract i iteMap
                       ( (cNode, cNodes, cEdges)
                        ,(tNode, tNodes, tEdges)
                        ,(eNode, eNodes, eEdges)) <- liftM3 (,,) (go x) (go y) (go z)
                       return (i, (i, frz c) : cNodes ++ tNodes ++ eNodes
                              ,(cNode, i, "if")
                               : (tNode, i, "then")
                               : (eNode, i, "else")
                               : cEdges ++ tEdges ++ eEdges)

    go c@(CEq i) = extract i eqMap >>= tupM2 go >>= addKids c
    go c@(CLt i) = extract i ltMap >>= tupM2 go >>= addKids c
    go c@(CNat i) = return (i, [(i, frz c)], [])

    addKids ccode ((lNode, lNodes, lEdges), (rNode, rNodes, rEdges)) =
        let i = circuitHash ccode
        in return (i, (i, frz ccode) : lNodes ++ rNodes,
                      (lNode, i, "l") : (rNode, i, "r") : lEdges ++ rEdges)
    tupM2 f (x, y) = liftM2 (,) (f x) (f y)

    frz (CVar i) = "v" ++ show i
    frz (CExist i) = "?" ++ show i
    frz CFalse{} = "false"
    frz CTrue{}  = "true"
    frz CNot{}   = "not"
    frz CAnd{} = "/\\"
    frz COr{}  = "\\/"
    frz CIff{} = "<->"
    frz COnlyif{} = "->"
    frz CXor{} = "xor"
    frz CIte{} = "if-then-else"
    frz (CNat c) = "n" ++ show c
    frz CEq{} = "=="
    frz CLt{} = "<"

    extract code f = do
        maps <- ask
        let lookupError = error $ "shareGraph: unknown code: " ++ show code
        case Bimap.lookup code (f maps) of
          Nothing -> lookupError
          Just x  -> return x

-- ** Circuit simplification

-- | Performs obvious constant propagations.
simplifyTree :: Eq v => Tree v -> Tree v
simplifyTree l@(TLeaf _) = l
simplifyTree TFalse      = TFalse
simplifyTree TTrue       = TTrue
simplifyTree (TNot t) =
    let t' = simplifyTree t
    in case t' of
         TTrue  -> TFalse
         TFalse -> TTrue
         _      -> TNot t'
simplifyTree (TAnd l r) =
    let l' = simplifyTree l
        r' = simplifyTree r
    in case l' of
         TFalse -> TFalse
         TTrue  -> case r' of
           TTrue  -> TTrue
           TFalse -> TFalse
           _      -> r'
         _      -> case r' of
           TTrue -> l'
           TFalse -> TFalse
           _ -> TAnd l' r'
simplifyTree (TOr l r) =
    let l' = simplifyTree l
        r' = simplifyTree r
    in case l' of
         TFalse -> r'
         TTrue  -> TTrue
         _      -> case r' of
           TTrue  -> TTrue
           TFalse -> l'
           _      -> TOr l' r'
simplifyTree (TXor l r) =
    let l' = simplifyTree l
        r' = simplifyTree r
    in case l' of
         TFalse -> r'
         TTrue  -> case r' of
           TFalse -> TTrue
           TTrue  -> TFalse
           _      -> TNot r'
         _      -> TXor l' r'
simplifyTree (TIff l r) =
    let l' = simplifyTree l
        r' = simplifyTree r
    in case l' of
         TFalse -> case r' of
           TFalse -> TTrue
           TTrue  -> TFalse
           _      -> l' `TIff` r'
         TTrue  -> case r' of
           TTrue  -> TTrue
           TFalse -> TFalse
           _      -> l' `TIff` r'
         _ -> l' `TIff` r'
simplifyTree (l `TOnlyIf` r) =
    let l' = simplifyTree l
        r' = simplifyTree r
    in case l' of
         TFalse -> TTrue
         TTrue  -> r'
         _      -> l' `TOnlyIf` r'
simplifyTree (TIte x t e) =
    let x' = simplifyTree x
        t' = simplifyTree t
        e' = simplifyTree e
    in case x' of
         TTrue  -> t'
         TFalse -> e'
         _      -> TIte x' t' e'

simplifyTree t@(TEq x y) = if x == y then TTrue  else t
simplifyTree t@(TLt x y) = if x == y then TFalse else t
simplifyTree t@TNat{}    = t

-- ** Convert circuit to CNF

data CNFState = CNFS{ toCnfVars :: !([Var])
                      -- ^ infinite fresh var source, starting at 1
                    , toCnfMap  :: !(Bimap Var CCode)
                      -- ^ record var mapping
                    , toBitMap  :: !(Map CCode [Var])
                      -- ^ mapping to binary representation of naturals
                    , numCnfClauses :: !Int
                    }

emptyCNFState :: CNFState
emptyCNFState = CNFS{ toCnfVars = [V 1 ..]
                    , numCnfClauses = 0
                    , toCnfMap = Bimap.empty
                    , toBitMap = Map.empty}

findVar' :: MonadState CNFState m => CCode -> (Lit -> m a) -> (Lit -> m a) -> m a
findVar' ccode kfound knot = do
    m <- gets toCnfMap
    v:vs <- gets toCnfVars
    case Bimap.lookupR ccode m of
      Nothing -> do modify $ \s -> s{ toCnfMap = Bimap.insert v ccode m
                                    , toCnfVars = vs }
                    knot $ lit v
      Just v'  -> kfound $ lit v'

recordVar :: MonadState CNFState m => CCode -> m Lit -> m Lit
recordVar ccode comp = do
    m <- gets toCnfMap
    case Bimap.lookupR ccode m of
      Nothing -> do l <- comp
                    modify $ \s -> s{ toCnfMap = Bimap.insert (var l) ccode (toCnfMap s) }
                    return l
      Just v  -> return (lit v)

-- | A circuit problem packages up the CNF corresponding to a given
-- `FrozenShared' circuit, and the mapping between the variables in the CNF and
-- the circuit elements of the circuit.

data ECircuitProblem v = ECircuitProblem
    { eproblemCnf     :: CNF
    , eproblemCircuit :: !(FrozenShared v)
    , eproblemCodeMap :: !(Bimap Var CCode)
    , eproblemBitMap  :: !(Map Var (CCode,Int))
    }

-- | Efficient conversion to conjunctive normal form
toCNF :: (Ord v, Show v) => FrozenShared v -> ECircuitProblem v
toCNF c@(FrozenShared !sharedCircuit !circuitMaps) = let
    (l,m,cnf) = runRWS (go sharedCircuit) circuitMaps emptyCNFState

    bitMap = Map.fromList [ (v, (c,i)) | (c,vv) <- Map.toList (toBitMap m), (v,i) <- zip vv [0..]]

    in ECircuitProblem
       { eproblemCnf = CNF { numVars    = pred $ unVar $ head (toCnfVars m)
                           , numClauses = numCnfClauses m + 1
                           , clauses    = [l]:cnf }
       , eproblemCircuit = c
       , eproblemCodeMap = toCnfMap m
       , eproblemBitMap  = bitMap}
  where
    bitWidth  = fst . head
              . dropWhile ( (< Bimap.size (natMap circuitMaps)) . snd )
              . zip [1..] . iterate (*2)
              $ 2

    writeClauses cc = incC (length cc) >> tell cc

    -- Returns l where {l} U the accumulated c is CNF equisatisfiable with the input
    -- circuit.  Note that CNF conversion only has cases for And, Or, Not, True,
    -- False, and Var circuits.  We therefore remove the complex circuit before
    -- passing stuff to this function.
    go c@(CVar{})   = findVar' c goOn goOn
    go c@CExist{}   = findVar' c goOn goOn
    go   (CTrue{})  = true
    go   (CFalse{}) = false
--     -- x <-> -y
--     --   <-> (-x, -y) & (y, x)
    go c@(CNot i) =  findVar' c goOn $ \notLit -> do
        eTree  <- extract i notMap
        eLit   <- go eTree
        writeClauses [  [negate notLit, negate eLit]
                     ,   [eLit, notLit]
                     ]
        return notLit

--     -- x <-> (y | z)
--     --   <-> (-y, x) & (-z, x) & (-x, y, z)
    go c@(COr i) = findVar' c goOn $ \orLit -> do
        (l, r) <- extract i orMap
        lLit <- go l
        rLit <- go r

        writeClauses [  [negate lLit, orLit]
                     ,  [negate rLit, orLit]
                     ,  [negate orLit, lLit, rLit]]

        return orLit

--     -- x <-> (y & z)
--     --   <-> (-x, y), (-x, z) & (-y, -z, x)
    go c@(CAnd i) = findVar' c goOn $ \andLit -> do
        (l, r) <- extract i andMap
        lLit <- go l
        rLit <- go r

        writeClauses [  [negate andLit, lLit]
                     ,  [negate andLit, rLit]
                     ,  [negate lLit, negate rLit, andLit]]

        return andLit

    go c@(CXor i) = recordVar c $ do
        (l,r) <- extract i xorMap
        lLit <- go l
        rLit <- go r
        (lLit `or` rLit) `andM` notM (lLit `and` rLit)

    go c@(COnlyif i) = recordVar c $ do
        (l,r) <- extract i onlyifMap
        lLit <- go l
        rLit <- go r
        (negate lLit `or` rLit)

    go c@(CIff i) = recordVar c $ do
        (l,r) <- extract i iffMap
        lLit <- go l
        rLit <- go r
        iff lLit rLit

    go c@(CIte i) = recordVar c $ do
        (c,t,e) <- extract i iteMap
        cLit <- go c
        tLit <- go t
        eLit <- go e
        ite cLit tLit eLit

    go c@(CEq i) = recordVar c $ do
        (nl,nr) <- extract i eqMap
        ll      <- findNat nl
        rr      <- findNat nr
        eq ll rr

    go c@(CLt i) = recordVar c $ do
        (nl,nr) <- extract i ltMap
        ll      <- findNat nl
        rr      <- findNat nr
        lt ll rr

    go c = do
        m <- ask
        error $  "go bug: unknown code: " ++ show c
              ++ " with maps:\n" ++ show (m{hashCount=[]})

    true = findVar' (CTrue trueHash) goOn $ \l -> do
        writeClauses [[l]]
        return l

    false = findVar' (CFalse falseHash) goOn $ \l -> do
        writeClauses  [ [negate l]]
        return l


    orM l r = do { vl <- l; vr <- r; or vl vr}
    or lLit rLit = do
        me <- exist
        writeClauses [  [negate lLit, me]
                     ,  [negate rLit, me]
                     ,  [negate me, lLit, rLit]]

        return me

    andM l r = do { vl <- l; vr <- r; and vl vr}
    and lLit rLit =  do
        me <- exist
        writeClauses [  [negate me, lLit]
                     ,  [negate me, rLit]
                     ,  [negate lLit, negate rLit,me]]

        return me

    notM = liftM negate

    iff lLit rLit = (negate lLit `or` rLit) `andM` (negate rLit `or` lLit)
    ite cLit tLit eLit = (cLit `and` tLit) `orM` (negate cLit `and` eLit)

    eq [] []         = true
    eq [] rr         = notM $ foldr orM false (map return rr)
    eq ll []         = notM $ foldr orM false (map return ll)
    eq (l:ll) (r:rr) = iff l r `andM` eq ll rr

    lt [] []         = false
    lt _ []          = false
    lt [] rr         = foldr orM false $ map return rr
    lt (l:ll) (r:rr) = lt ll rr `orM` ((negate l `and` r) `andM` eq ll rr)

    incC i = modify $ \m ->  m{numCnfClauses = numCnfClauses m + i}

    extract code f = do
        m <- asks f
        case Bimap.lookup code m of
          Nothing -> error $ "toCNF: unknown code: " ++ show code
          Just x  -> return x

    findNat ccode@CNat{} = do
        bm <- gets toBitMap
        case Map.lookup ccode bm of
          Just bits -> return (map lit bits)
          Nothing -> do
              bits <- replicateM bitWidth exist
              modify $ \s -> s{ toBitMap  = Map.insert ccode (map var bits) bm }
              return bits
    findNat code = error $ "toCNF/findNat: expected a CNat code, but instead got: " ++ show code

    goOn c = return c

    exist = do
       v:vs <- gets toCnfVars
       modify $ \s -> s{toCnfVars=vs}
       return (lit v)

-- | Replace Nat constraints with propositional constraints over the bits of the naturals.
--   Returns the new circuit, together with a mapping from variables representing naturals
--   to a list of their bits lsb first.
removeNats :: (Ord v, Show v) => [v] -> FrozenShared v -> (FrozenShared v, Map v [v])
removeNats freshvars f@(FrozenShared _code maps) = removeNats' bitwidth freshvars f
  where
  bitwidth = fst . head . dropWhile ( (< Bimap.size (natMap maps)) . snd) . zip [1..] . iterate (*2) $ 2

removeNats' :: (Ord v, Show v) => Int -> [v] -> FrozenShared v -> (FrozenShared v, Map v [v])
removeNats' bitwidth freshvars (FrozenShared code maps)
  -- We walk the graph replacing order constraints with freshly made propositional constraints
  -- In order to avoid replacing the same constraint several times, we keep a table
  -- of constraints so far replaced
   = assert disjoint $
     ( FrozenShared code' maps'{natMap = Bimap.empty}
     , bitnats)
   where
  (code',(maps',_)) = runState (go' code) (maps, Map.empty)

  bitnats  = Map.fromList (Bimap.elems (natMap maps) `zip` chunk bitwidth freshvars)
  disjoint = all (`notElem` Map.elems (Bimap.toMap $ varMap maps))  (concat $ Map.elems $ bitnats)
  lookupBits c = fromJust $ Map.lookup (getChildren c (natMap maps)) bitnats

  go c = do
    table <- gets snd
    case Map.lookup c table of
      Just c' -> return c'
      _       -> go' c
  go' c@CTrue{}  = return c
  go' c@CFalse{} = return c
  go' c@CVar{}   = return c
  go' c@CExist{} = return c
  go' c@CNot{}   = updateC go c notMap (\s e -> s{notMap = e})
  go' c@COr{}    = updateC (onTupM go)  c orMap (\s e -> s{orMap = e})
  go' c@CXor{}   = updateC (onTupM go)  c xorMap (\s e -> s{xorMap = e})
  go' c@CAnd{}   = updateC (onTupM go)  c andMap (\s e -> s{andMap = e})
  go' c@CIff{}   = updateC (onTupM go)  c iffMap (\s e -> s{iffMap = e})
  go' c@COnlyif{}= updateC (onTupM go)  c onlyifMap (\s e -> s{onlyifMap = e})
  go' c@CIte{}   = updateC (onTripM go) c iteMap (\s e -> s{iteMap = e})
  go'   CNat{}   = error "removeNats: unexpected"
  go' c@CEq{}    = f c eqMap eq
  go' c@CLt{}    = f c ltMap lt

  f c cmpMap cmp = do
    s       <- gets fst
    let (na,nb) = onTup lookupBits $ getChildren c (cmpMap s)
    let (c',s') = runState (unShared $ cmp na nb) s
    modify.first.const $ s'
    modify.second $ Map.insert c c'
    return c'

  updateC f c prj upd = do
    s  <- gets fst
    let ab = getChildren c (prj s)
    ab' <- f ab
    when (ab' /= ab) $
         modify.first $ \s' -> upd s' (Bimap.insert (circuitHash c) ab' (prj s'))
    return c

  onTupM f (x,y) = do {x' <- f x; y' <- f y; return (x',y')}
  onTripM f (x,y,z) = do {x' <- f x; y' <- f y; z' <- f z; return (x',y',z')}


  eq (p:pp) (q:qq) = iff (input p) (input q) `and` eq pp qq
  eq [] [] = true
  eq [] qq = not $ orL $ map input qq
  eq pp [] = not $ orL $ map input pp

  lt (p:pp) (q:qq) = lt pp qq `or` (not (input p) `and` input q `and` eq pp qq)
  lt [] [] = false
  lt [] qq = orL $ map input qq
  lt _  [] = false

-- | Returns an equivalent circuit with no iff, xor, onlyif, ite, nat, eq and lt nodes.
removeComplex :: (Ord v, Show v, ExistCircuit c, Co c v) => [v] -> FrozenShared v -> (c v, Map v [v])
removeComplex freshVars (FrozenShared code maps) = assert disjoint $ (go code, bitnats)
  where

  -- remove all order constraints by encoding them as propositional constrains on binary digits
  bitwidth = fst . head . dropWhile ( (< Bimap.size (natMap maps)) . snd) . zip [1..] . iterate (*2) $ 2
  bitnats  = Map.fromList (Bimap.elems (natMap maps) `zip` chunk bitwidth freshVars)
  disjoint = all (`notElem` Bimap.elems (varMap maps))  (concat $ Map.elems bitnats)
  lookupBits c = fromJust $ Map.lookup (getChildren c (natMap maps)) bitnats

  go (CTrue{})  = true
  go (CFalse{}) = false
  go c@(CVar{}) = input $ getChildren c (varMap maps)
  go   CExist{} = exists id
  go c@(COr{})  = uncurry or (go `onTup` getChildren c (orMap maps))
  go c@(CAnd{}) = uncurry and (go `onTup` getChildren c (andMap maps))
  go c@(CNot{}) = not . go $ getChildren c (notMap maps)
  go c@(CXor{}) =
      let (l, r) = go `onTup` getChildren c (xorMap maps)
      in (l `or` r) `and` not (l `and` r)
  go c@(COnlyif{}) =
      let (p, q) = go `onTup` getChildren c (onlyifMap maps)
      in not p `or` q
  go c@(CIff{}) =
      let (p, q) = go `onTup` getChildren c (iffMap maps)
      in (not p `or` q) `and` (not q `or` p)
  go c@(CIte{}) =
      let (cc, tc, ec) = getChildren c (iteMap maps)
          (cond, t, e) = (go cc, go tc, go ec)
      in (cond `and` t) `or` (not cond `and` e)

  go  CNat{} = typeError "removeComplex: expected a boolean."
  go c@CEq{}
      | (a@CNat{}, b@CNat{}) <- getChildren c (eqMap maps)
      , na <- lookupBits a
      , nb <- lookupBits b
      = eq na nb

      | otherwise
      = typeError "removeComplex: expected a boolean."

  go c@(CLt{})
      | (a@CNat{}, b@CNat{}) <- getChildren c (ltMap maps)
      , na <- lookupBits a
      , nb <- lookupBits b
      = lt na nb

      | otherwise
      = typeError "removeComplex: expected a boolean."
  eq (p:pp) (q:qq) =      (     (not (input p) `and` not (input q))
                           `or` (input p `and` input q)
                          )
                     `and` eq pp qq
  eq [] qq = not $ orL $ map input qq
  eq pp [] = not $ orL $ map input pp

  lt (p:pp) (q:qq) = lt pp qq `or` (not (input p) `and` input q `and` eq pp qq)
  lt [] qq = orL $ map input qq
  lt _  [] = false



onTup :: (a -> b) -> (a, a) -> (b, b)
onTup f (x, y) = (f x, f y)

-- | Projects a funsat `Solution' back into the original circuit space,
-- returning a boolean environment containing an assignment of all circuit
-- inputs to true and false.
projectECircuitSolution :: (Ord v) => Solution -> ECircuitProblem v -> BIEnv v
projectECircuitSolution sol ECircuitProblem{ eproblemCodeMap = codeMap
                                           , eproblemBitMap  = bitsMap
                                           , eproblemCircuit = FrozenShared _ maps}

  = case sol of
      Sat lits   -> projectLits lits
      Unsat lits -> projectLits lits

  where

  projectLits lits = Map.map Right vm `mappend`
                     Map.map (Left . fromBinary . map snd . sortBy (compare `on` fst)) bm
      -- only the lits whose vars are (varMap maps) go to benv
    where
--    intermediates :: (Map v Bool, Map v [(Int,Bool)])
    (vm, bm) =
      foldl (\m l -> case litHash l of
                       Var h   -> insertVar h l m
                       Bit h_i -> insertNat h_i l m
                       Auxiliar-> m)
            (initiallyAllFalseMap, initiallyAllZeroMap)
            (litAssignment lits)

    initiallyAllFalseMap = Map.fromList [(v,False) | v <- Bimap.elems (varMap maps)]
    initiallyAllZeroMap  = Map.empty -- 8fromList [(v,0)     | v <- Bimap.elems (natMap maps)]

    insertVar h l (mb,mn) = (mb', mn) where
       mb' = case Bimap.lookup h (varMap maps) of
                             Nothing -> mb
                             Just v  -> Map.insert v (litSign l) mb

    insertNat (h,i) l (mb,mn) = (mb, mn') where
        mn' = case Bimap.lookup h (natMap maps) of
                          Nothing -> mn
                          Just n  -> Map.insertWith (++) n [(i,litSign l)] mn

    litHash l = case Bimap.lookup (var l) codeMap of
                  Nothing -> case Map.lookup (var l) bitsMap of
                               Just (code,bit) -> Bit (circuitHash code, bit)
                               Nothing         -> Auxiliar
                  Just code -> Var (circuitHash code)

    on cmp f x y = cmp (f x) (f y)

reconstructNatsFromBits :: Ord v => [(v, [v])] -> BIEnv v -> BIEnv v
reconstructNatsFromBits bitnats bienv = bienv'
 where
  bienv' = bienv `mappend`
           Map.fromList [ (v, Left nat)
                           | (v, bits) <- bitnats
                           , let nat = fromBinary $
                                       map (\v -> fromRight $ Map.findWithDefault (Right False) v bienv) bits
                          ]
  fromRight (Right x) = x
  fromRight (Left _) = error "fromRight"

data ProjectionCase = Var CircuitHash | Bit (CircuitHash, Int) | Auxiliar

typeError :: String -> a
typeError msg = error (msg ++ "\nPlease send an email to the pepeiborra@gmail.com requesting a typed circuit language.")
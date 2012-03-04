{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}

-- | A circuit is a standard one of among many ways of representing a
-- propositional logic formula.  This module provides a flexible circuit type
-- class and various representations that admit efficient conversion to funsat
-- CNF.
--
-- The implementation for this module was adapted from
-- <http://okmij.org/ftp/Haskell/DSLSharing.hs>.
module Funsat.Circuit
    (
    -- ** Circuit type class
      Circuit(..)
    , CastCircuit(..)

    -- ** explicit sharing circuit
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
    , simplifyTree

    -- ** Explicit graph circuit
    , Graph
    , runGraph
    , shareGraph
    , NodeType(..)

    -- ** Circuit evaluator
    , BEnv, BIEnv
    , Eval, EvalF(..)
    , runEval

    -- ** Convert circuit to CNF
    , CircuitProblem(..)
    , toCNF
    , projectCircuitSolution
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
import Control.Monad.Reader
import Control.Monad.State.Strict hiding ((>=>), forM_)
import Control.Monad.RWS
import Data.Bimap( Bimap )
import Data.Foldable (Foldable, foldMap)
import Data.List( nub )
import Data.Map( Map )
import Data.Maybe()
import Data.Ord()
import Data.Set( Set )
import Data.Traversable (Traversable, traverse, fmapDefault, foldMapDefault)
import Funsat.Types( CNF(..), Lit(..), Var(..), var, lit, Solution(..), litSign, litAssignment )
import Prelude hiding( not, and, or )

import qualified Data.Bimap as Bimap
import qualified Data.Foldable as Foldable
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Prelude as Prelude

import GHC.Prim (Constraint)

-- * Circuit representation


-- | A class representing a grammar for logical circuits.  Default
-- implemenations are indicated.
class Circuit repr where
    type Co repr var :: Constraint
    true  :: Co repr var => repr var
    false :: Co repr var => repr var
    input :: Co repr var => var -> repr var
    not   :: Co repr var => repr var -> repr var

    -- | Defined as @`and' p q = not (not p `or` not q)@.
    and   :: Co repr var => repr var -> repr var -> repr var
    and p q = not (not p `or` not q)

    -- | Defined as @`or' p q = not (not p `and` not q)@.
    or    :: Co repr var => repr var -> repr var -> repr var
    or p q = not (not p `and` not q)

    orL, andL :: Co repr var => [repr var] -> repr var
    orL  = foldr or false
    andL = foldr and true

-- | Instances of `CastCircuit' admit converting one circuit representation to
-- another.
class Circuit cOut => CastCircuit c cOut where
    type CastCo c cOut var :: Constraint
    type CastCo c cOut var = Co cOut var
    castCircuit :: (CastCo c cOut var, Ord var) => c var -> cOut var

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

instance Circuit c => CastCircuit Shared c where
    castCircuit = castCircuit . runShared

instance Circuit c => CastCircuit FrozenShared c where
    castCircuit (FrozenShared code maps) = go code
      where
        go (CTrue{})     = true
        go (CFalse{})    = false
        go c@(CVar{})    = input $ getChildren c (varMap maps)
        go c@(CAnd{})    = uncurry and    . go2 $ getChildren c (andMap maps)
        go c@(COr{})     = uncurry or     . go2 $ getChildren c (orMap maps)
        go c@(CNot{})    = not            . go  $ getChildren c (notMap maps)

        go2 = (go `onTup`)

        onTup f (x,y) = (f x, f y)

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
           | CAnd    { circuitHash :: !CircuitHash }
           | COr     { circuitHash :: !CircuitHash }
           | CNot    { circuitHash :: !CircuitHash }
             deriving (Eq, Ord, Show, Read)

-- | Maps used to implement the common-subexpression sharing implementation of
-- the `Circuit' class.  See `Shared'.
data CMaps v = CMaps
    { hashCount :: ![CircuitHash]
    -- ^ Source of unique IDs used in `Shared' circuit generation.  Should not
    -- include 0 or 1.

    , varMap    :: !(Bimap CircuitHash v)
     -- ^ Mapping of generated integer IDs to variables.

    , andMap    :: !(Bimap CircuitHash (CCode, CCode))
    , orMap     :: !(Bimap CircuitHash (CCode, CCode))
    , notMap    :: !(Bimap CircuitHash CCode)
    }
               deriving (Eq, Show)

-- | A `CMaps' with an initial `hashCount' of 2.
emptyCMaps :: CMaps v
emptyCMaps = CMaps
    { hashCount = [2 ..]
    , varMap    = Bimap.empty
    , andMap    = Bimap.empty
    , orMap     = Bimap.empty
    , notMap    = Bimap.empty
    }

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
            -- trace "updating map" (return ())
            return (cons c))
        (return . cons) $ lookupv x (prj s)

instance Circuit Shared where
    type Co Shared var = Ord var
    false = Shared falseS
    true  = Shared trueS
    input v = Shared $ recordC CVar varMap (\s e -> s{ varMap = e }) v
    and = liftShared2 and_ where
        and_ c@CFalse{} _ = return c
        and_ _ c@CFalse{} = return c
        and_ CTrue{} c  = return c
        and_ c CTrue{}  = return c
        and_ hl hr = recordC CAnd andMap (\s e -> s{ andMap = e}) (hl, hr)

    or = liftShared2 or_ where
        or_ c@CTrue{} _ = return c
        or_ _ c@CTrue{} = return c
        or_ CFalse{} c  = return c
        or_ c CFalse{}  = return c
        or_ hl hr = recordC COr orMap (\s e -> s{ orMap = e }) (hl, hr)
    not = liftShared not_ where
        not_ CTrue{}  = falseS
        not_ CFalse{} = trueS
        not_ h        = recordC CNot notMap (\s e' -> s{ notMap = e' }) h


{-# INLINE liftShared #-}
liftShared :: (CCode -> State (CMaps v) CCode) -> Shared v -> Shared v
liftShared f a = Shared $ do {h <- unShared a; f h}

{-# INLINE liftShared2 #-}
liftShared2 :: (CCode -> CCode -> State (CMaps v) CCode) -> Shared v -> Shared v -> Shared v
liftShared2 f a b = Shared $ do
  va <- unShared a
  vb <- unShared b
  f va vb

falseS, trueS :: State (CMaps v) CCode
falseS = return $ CFalse falseHash
trueS  = return $ CTrue trueHash


{-
-- | An And-Inverter graph edge may complement its input.
data AIGEdge = AIGPos | AIGNeg
type AIGGr g v = g (Maybe v) AIGEdge
-- | * 0 is the output.
data AndInverterGraph gr v = AIG
    { aigGraph :: AIGGr gr v
      -- ^ Node 0 is the output node.  Node 1 is hardwired with a 'true' input.
      -- The edge from Node 1 to 0 may or may not be complemented.

    , aigInputs :: [G.Node]
      -- ^ Node 1 is always an input set to true.
    }

instance (G.Graph gr, Show v, Ord v) => Monoid (AndInverterGraph gr v) where
   mempty = true
   mappend a1 a2 =
        AIG{ aigGraph  = mergedGraph
           , aigInputs = nub (aigInputs a1 ++ aigInputs a2) }
      where
      mergedGraph = G.mkGraph
                    (G.labNodes (aigGraph a1) ++ G.labNodes (aigGraph a2))
                    (G.labEdges (aigGraph a1) ++ G.labEdges (aigGraph a2))

instance (G.Graph gr) => Circuit (AndInverterGraph gr) where
    true = AIG{ aigGraph = G.mkGraph [(0,Nothing), (1,Nothing)] [(1, 0, AIGPos)]
              , aigInputs = [1] }

    false = AIG{ aigGraph = G.mkGraph [(0,Nothing), (1,Nothing)] [(1, 0, AIGNeg)]
               , aigInputs = [1] }

    input v = let [n] = G.newNodes 1 true
              in AIG{ aigGraph = G.insNode (n, Just v) true
                    , aigInputs `= [n, 1] }
-}

--     and l r = let g' = l `mappend` r
--                   [n] = G.newNodes 1 g'
--               in G.insNode (n, Nothing)

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
               deriving (Show, Eq, Ord)

foldTree :: (t -> v -> t) -> t -> Tree v -> t
foldTree _ i TTrue        = i
foldTree _ i TFalse       = i
foldTree f i (TLeaf v)    = f i v
foldTree f i (TAnd t1 t2) = foldTree f (foldTree f i t1) t2
foldTree f i (TOr t1 t2)  = foldTree f (foldTree f i t1) t2
foldTree f i (TNot t)     = foldTree f i t

instance Functor Tree where fmap = fmapDefault
instance Foldable Tree where foldMap = foldMapDefault
instance Traversable Tree where
  traverse _ TTrue  = pure TTrue
  traverse _ TFalse = pure TFalse
  traverse f (TLeaf v) = TLeaf <$> f v
  traverse f (TNot t) = TNot <$> traverse f t
  traverse f (TAnd t1 t2) = TAnd <$> traverse f t1 <*> traverse f t2
  traverse f (TOr  t1 t2) = TOr  <$> traverse f t1 <*> traverse f t2

instance Circuit Tree where
    type Co Tree var = ()
    true  = TTrue
    false = TFalse
    input = TLeaf
    and   = TAnd
    or    = TOr
    not   = TNot

instance Circuit c => CastCircuit Tree c where
    castCircuit TTrue        = true
    castCircuit TFalse       = false
    castCircuit (TLeaf l)    = input l
    castCircuit (TAnd t1 t2) = and (castCircuit t1) (castCircuit t2)
    castCircuit (TOr t1 t2)  = or (castCircuit t1) (castCircuit t2)
    castCircuit (TNot t)     = not (castCircuit t)

-- ** Circuit evaluator

type BEnv v = Map v Bool
type BIEnv v = Map v (Either Int Bool)

-- | A circuit evaluator, that is, a circuit represented as a function from
-- variable values to booleans.
type Eval = EvalF (Either Int Bool)
newtype EvalF a v = Eval { unEval :: BIEnv v -> a }

-- | Evaluate a circuit given inputs.
runEval :: BEnv v -> Eval v -> Bool
runEval = (fromRight.) . flip unEval . Map.map Right

instance Circuit Eval where
    type Co Eval var = (Ord var, Show var)
    true    = Eval $ const $ Right True
    false   = Eval $ const $ Right False
    input v = Eval $ \env ->
                      Map.findWithDefault (Right False)
--                        (error $ "Eval: no such var: " ++ show v
--                                 ++ " in " ++ show env)
                         v env
    and c1 c2 = Eval (\env -> Right $ fromRight(unEval c1 env) && fromRight(unEval c2 env))
    or  c1 c2 = Eval (\env -> Right $ fromRight(unEval c1 env) || fromRight(unEval c2 env))
    not c     = Eval (\env -> Right $ Prelude.not $ fromRight(unEval c env))


fromRight :: Either Int Bool -> Bool
fromRight = (`either` id) (error "fromRight - Left.")

-- ** Graph circuit

-- | A circuit type that constructs a `G.Graph' representation.  This is useful
-- for visualising circuits, for example using the @graphviz@ package.
newtype Graph v = Graph
    { unGraph :: State Graph.Node (Graph.Node,
                                    [Graph.LNode (NodeType v)],
                                    [Graph.LEdge ()]) }

-- | Node type labels for graphs.
data NodeType v = NInput v
                | NTrue
                | NFalse
                | NAnd
                | NOr
                | NNot
                  deriving (Eq, Ord, Show, Read)

runGraph :: (G.DynGraph gr) => Graph v -> gr (NodeType v) ()
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
        return (n, (n, NNot) : nodes, (node, n, ()) : edges)

    and = binaryNode NAnd
    or  = binaryNode NOr

binaryNode :: NodeType v -> Graph v -> Graph v -> Graph v
{-# INLINE binaryNode #-}
binaryNode ty l r = Graph $ do
        (lNode, lNodes, lEdges) <- unGraph l
        (rNode, rNodes, rEdges) <- unGraph r
        n <- newNode
        return (n, (n, ty) : lNodes ++ rNodes,
                   (lNode, n, ()) : (rNode, n, ()) : lEdges ++ rEdges)


newNode :: State Graph.Node Graph.Node
newNode = do i <- get ; put (succ i) ; return i

{-
defaultNodeAnnotate :: (Show v) => LNode (FrozenShared v) -> [GraphViz.Attribute]
defaultNodeAnnotate (_, FrozenShared (output, cmaps)) = go output
  where
    go CTrue{}       = "true"
    go CFalse{}      = "false"
    go (CVar _ i)    = show $ extract i varMap
    go (CNot{})      = "NOT"
    go (CAnd{hlc=h}) = maybe "AND" goHLC h
    go (COr{hlc=h})  = maybe "OR" goHLC h

    goHLC (Xor{})    = "XOR"
    goHLC (Onlyif{}) = go (output{ hlc=Nothing })
    goHLC (Iff{})    = "IFF"

    extract code f =
        IntMap.findWithDefault (error $ "shareGraph: unknown code: " ++ show code)
        code
        (f cmaps)

defaultEdgeAnnotate = undefined

dotGraph :: (Graph gr) => gr (FrozenShared v) (FrozenShared v) -> DotGraph
dotGraph g = graphToDot g defaultNodeAnnotate defaultEdgeAnnotate

-}

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
    go c@(CTrue i)  = return (i, [(i, frz c)], [])
    go c@(CFalse i) = return (i, [(i, frz c)], [])
    go c@(CNot i) = do
        (child, nodes, edges) <- extract i notMap >>= go
        return (i, (i, frz c) : nodes, (child, i, frz c) : edges)
    go c@(CAnd i) = extract i andMap >>= tupM2 go >>= addKids c
    go c@(COr i) = extract i orMap >>= tupM2 go >>= addKids c

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

-- ** Convert circuit to CNF

-- this data is private to toCNF.
data CNFResult = CP !Lit [Set Lit]
data CNFState = CNFS{ toCnfVars :: !([Var])
                      -- ^ infinite fresh var source, starting at 1
                    , toCnfMap  :: !(Bimap Var CCode)
                      -- ^ record var mapping
                    , numCnfClauses :: !Int
                    }

emptyCNFState :: CNFState
emptyCNFState = CNFS{ toCnfVars = [V 1 ..]
                    , numCnfClauses = 0
                    , toCnfMap = Bimap.empty}

findVar :: MonadState CNFState m => CCode -> (Lit -> m a) -> (Lit -> m a) -> m a
findVar ccode kfound knot = do
    m <- gets toCnfMap
    v:vs <- gets toCnfVars
    case Bimap.lookupR ccode m of
      Nothing -> do modify $ \s -> s{ toCnfMap = Bimap.insert v ccode m
                                    , toCnfVars = vs }
                    knot $ lit v
      Just v'  -> kfound $ lit v'

-- | A circuit problem packages up the CNF corresponding to a given
-- `FrozenShared' circuit, and the mapping between the variables in the CNF and
-- the circuit elements of the circuit.
data CircuitProblem v = CircuitProblem
    { problemCnf     :: CNF
    , problemCircuit :: !(FrozenShared v)
    , problemCodeMap :: !(Bimap Var CCode)
    }

-- | Produces a CNF formula that is satisfiable if and only if the input circuit
-- is satisfiable.  /Note that it does not produce an equivalent CNF formula./
-- It is not equivalent in general because the transformation introduces
-- variables into the CNF which were not present as circuit inputs.  (Variables
-- in the CNF correspond to circuit elements.)  Returns equisatisfiable CNF
-- along with the frozen input circuit, and the mapping between the variables of
-- the CNF and the circuit elements.
--
-- The implementation uses the Tseitin transformation, to guarantee that the
-- output CNF formula is linear in the size of the circuit.  Contrast this with
-- the naive DeMorgan-laws transformation which produces an exponential-size CNF
-- formula.
toCNF :: (Ord v, Show v) => FrozenShared v -> CircuitProblem v
toCNF c@(FrozenShared sharedCircuit circuitMaps) =
    let (cnf, m, ()) = (\m -> runRWS m circuitMaps emptyCNFState) $ do
                     (CP l theClauses) <- toCNF' sharedCircuit
                     return $  (Set.singleton l : theClauses)

        nv = pred $ unVar $ head $ toCnfVars m

    in CircuitProblem
       { problemCnf = CNF { numVars    = nv
                          , numClauses = numCnfClauses m + 1
                          , clauses    = map Foldable.toList cnf }
       , problemCircuit = c
       , problemCodeMap = toCnfMap m}
  where
    -- Returns (CP l c) where {l} U c is CNF equisatisfiable with the input
    -- circuit.  Note that CNF conversion only has cases for And, Or, Not, True,
    -- False, and Var circuits.  We therefore remove the complex circuit before
    -- passing stuff to this function.
    toCNF' c@(CVar{})   = findVar c goOn goOn
    toCNF' c@(CTrue{})  = findVar c goOn $ \l -> do
        incC 1
        return (CP l [Set.singleton  l])
    toCNF' c@(CFalse{}) = findVar c goOn $ \l -> do
        incC 1
        return (CP l [Set.singleton (negate l)])

--     -- x <-> -y
--     --   <-> (-x, -y) & (y, x)
    toCNF' c@(CNot i) = findVar c goOn $ \notLit -> do
        eTree <- extract i notMap
        (CP eLit eCnf) <- toCNF' eTree
        incC 2
        return
          (CP notLit
               ( Set.fromList [negate notLit, negate eLit]
               : Set.fromList [eLit, notLit]
               : eCnf))

--     -- x <-> (y | z)
--     --   <-> (-y, x) & (-z, x) & (-x, y, z)
    toCNF' c@(COr i) = findVar c goOn $ \orLit -> do
        (l, r) <- extract i orMap
        (CP lLit lCnf) <- toCNF' l
        (CP rLit rCnf) <- toCNF' r
        incC 3
        return
          (CP orLit
              ( Set.fromList [negate lLit, orLit]
              : Set.fromList [negate rLit, orLit]
              : Set.fromList [negate orLit, lLit, rLit]
              : lCnf ++ rCnf))

--     -- x <-> (y & z)
--     --   <-> (-x, y), (-x, z) & (-y, -z, x)
    toCNF' c@(CAnd i) = findVar c goOn $ \andLit -> do
        (l, r) <- extract i andMap
        (CP lLit lCnf) <- toCNF' l
        (CP rLit rCnf) <- toCNF' r
        incC 3
        return
          (CP andLit
             ( Set.fromList [negate andLit, lLit]
             : Set.fromList [negate andLit, rLit]
             : Set.fromList [negate lLit, negate rLit, andLit]
             : lCnf ++ rCnf))

    incC i = modify $ \m -> m{numCnfClauses = numCnfClauses m + i}

    goOn c = return (CP c [])

    extract code f = do
        m <- asks f
        case Bimap.lookup code m of
          Nothing -> error $ "toCNF: unknown code: " ++ show code
          Just x  -> return x

-- | Projects a funsat `Solution' back into the original circuit space,
-- returning a boolean environment containing an assignment of all circuit
-- inputs to true and false.
projectCircuitSolution :: (Ord v) => Solution -> CircuitProblem v -> BEnv v
projectCircuitSolution sol pblm = case sol of
                                    Sat lits   -> projectLits lits
                                    Unsat lits -> projectLits lits
  where
  projectLits lits =
      -- only the lits whose vars are (varMap maps) go to benv
      foldl (\m l -> case Bimap.lookup (litHash l) (varMap maps) of
                       Nothing -> m
                       Just v  -> Map.insert v (litSign l) m)
            Map.empty
            (litAssignment lits)
    where
    (FrozenShared _ maps) = problemCircuit pblm
    litHash l = case Bimap.lookup (var l) (problemCodeMap pblm) of
                  Nothing -> error $ "projectSolution: unknown lit: " ++ show l
                  Just code -> circuitHash code

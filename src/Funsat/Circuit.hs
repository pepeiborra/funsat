

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
    , simplifyTree

    -- ** Explicit graph circuit
    , Graph
    , runGraph
    , shareGraph
    , NodeType(..)
    , EdgeType(..)

    -- ** Circuit evaluator
    , BEnv
    , Eval(..)
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


import Control.Monad.Reader
import Control.Monad.State.Lazy hiding ((>=>), forM_)
import Data.Bimap( Bimap )
import Data.List( nub, foldl')
import Data.Map( Map )
import Data.Maybe()
import Data.Ord()
import Data.Set( Set )
import Funsat.Types( CNF(..), Lit(..), Var(..), var, lit, Solution(..), litSign, litAssignment )
import Prelude hiding( not, and, or )

import qualified Data.Bimap as Bimap
import qualified Data.Foldable as Foldable
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Prelude as Prelude



-- * Circuit representation


-- | A class representing a grammar for logical circuits.  Default
-- implemenations are indicated.
class Circuit repr where
    true  :: (Ord var, Show var) => repr var
    false :: (Ord var, Show var) => repr var
    input :: (Ord var, Show var) => var -> repr var
    not   :: (Ord var, Show var) => repr var -> repr var

    -- | Defined as @`and' p q = not (not p `or` not q)@.
    and   :: (Ord var, Show var) => repr var -> repr var -> repr var
    and p q = not (not p `or` not q)

    -- | Defined as @`or' p q = not (not p `and` not q)@.
    or    :: (Ord var, Show var) => repr var -> repr var -> repr var
    or p q = not (not p `and` not q)

    -- | If-then-else circuit.  @ite c t e@ returns a circuit that evaluates to
    -- @t@ when @c@ evaluates to true, and @e@ otherwise.
    --
    -- Defined as @(c `and` t) `or` (not c `and` f)@.
    ite :: (Ord var, Show var) => repr var -> repr var -> repr var -> repr var
    ite c t f = (c `and` t) `or` (not c `and` f)

    -- | Defined as @`onlyif' p q = not p `or` q@.
    onlyif :: (Ord var, Show var) => repr var -> repr var -> repr var
    onlyif p q = not p `or` q

    -- | Defined as @`iff' p q = (p `onlyif` q) `and` (q `onlyif` p)@.
    iff :: (Ord var, Show var) => repr var -> repr var -> repr var
    iff p q = (p `onlyif` q) `and` (q `onlyif` p)

    -- | Defined as @`xor' p q = (p `or` q) `and` not (p `and` q)@.
    xor :: (Ord var, Show var) => repr var -> repr var -> repr var
    xor p q = (p `or` q) `and` not (p `and` q)

    -- | Ordering constraints for binary represented (lsb first) naturals
    nat   :: (Ord var, Show var) => [var] -> repr var
    gt,lt,eq :: (Ord var, Show var) => repr var -> repr var -> repr var
{-
    eq (p:pp) (q:qq) = iff p q `and` eq pp qq
    eq [] [] = true
    eq [] qq = not $ foldr or false qq
    eq pp [] = not $ foldr or false pp

    lt (p:pp) (q:qq) = lt pp qq `or` (not p `and` q `and` eq pp qq)
    lt [] qq = not (foldr or false qq)
    lt _  [] = false
-}
    gt x y = not (lt x y) `and` not (eq x y)
--    lt x y = not (gt x y) `and` not (eq x y)


-- | Instances of `CastCircuit' admit converting one circuit representation to
-- another.
class CastCircuit c where
    castCircuit :: (Circuit cOut, Ord var, Show var) => c var -> cOut var


-- ** Explicit sharing circuit

-- The following business is for elimination of common subexpressions from
-- boolean functions.  Part of conversion to CNF.

-- | A `Circuit' constructed using common-subexpression elimination.  This is a
-- compact representation that facilitates converting to CNF.  See `runShared'.
newtype Shared v = Shared { unShared :: State (CMaps v) CCode }

-- | A shared circuit that has already been constructed.
data FrozenShared v = FrozenShared !CCode !(CMaps v) deriving (Eq, Show)

-- | Reify a sharing circuit.
runShared :: Shared v -> FrozenShared v
runShared = uncurry FrozenShared . (`runState` emptyCMaps) . unShared

instance CastCircuit Shared where
    castCircuit = castCircuit . runShared

instance CastCircuit FrozenShared where
    castCircuit (FrozenShared code maps) = go code
      where
        go (CTrue{})     = true
        go (CFalse{})    = false
        go c@(CVar{})    = input $ getChildren c (varMap maps)
        go c@(CAnd{})    = uncurry and . go2 $ getChildren c (andMap maps)
        go c@(COr{})     = uncurry or . go2 $ getChildren c (orMap maps)
        go c@(CNot{})    = not . go $ getChildren c (notMap maps)
        go c@(CXor{})    = uncurry xor . go2 $ getChildren c (xorMap maps)
        go c@(COnlyif{}) = uncurry onlyif . go2 $ getChildren c (onlyifMap maps)
        go c@(CIff{})    = uncurry iff . go2 $ getChildren c (iffMap maps)
        go c@(CIte{})    = uncurry3 ite . go3 $ getChildren c (iteMap maps)
        go c@CEq{}       = uncurry eq . go2 $ getChildren c (eqMap maps)
        go c@CLt{}       = uncurry lt . go2 $ getChildren c (ltMap maps)
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
    { hashCount :: [CircuitHash]
    -- ^ Source of unique IDs used in `Shared' circuit generation.  Should not
    -- include 0 or 1.

    , varMap    :: Bimap CircuitHash v
     -- ^ Mapping of generated integer IDs to variables.

    , andMap    :: Bimap CircuitHash (CCode, CCode)
    , orMap     :: Bimap CircuitHash (CCode, CCode)
    , notMap    :: Bimap CircuitHash CCode
    , xorMap    :: Bimap CircuitHash (CCode, CCode)
    , onlyifMap :: Bimap CircuitHash (CCode, CCode)
    , iffMap    :: Bimap CircuitHash (CCode, CCode)
    , iteMap    :: Bimap CircuitHash (CCode, CCode, CCode)
    , natMap    :: Bimap CircuitHash [v]
    , eqMap     :: Bimap CircuitHash (CCode, CCode)
    , ltMap     :: Bimap CircuitHash (CCode, CCode)
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
    , xorMap    = Bimap.empty
    , onlyifMap = Bimap.empty
    , iffMap    = Bimap.empty
    , iteMap    = Bimap.empty
    , natMap    = Bimap.empty
    , eqMap     = Bimap.empty
    , ltMap     = Bimap.empty }

-- | Find key mapping to given value.
lookupv :: Ord v => v -> Bimap Int v -> Maybe Int
lookupv = Bimap.lookupR

-- prj: "projects relevant map out of state"
-- upd: "stores new map back in state"
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
    false = Shared . return $ CFalse falseHash
    true  = Shared . return $ CTrue trueHash
    input v = Shared $ recordC CVar varMap (\s e -> s{ varMap = e }) v
    and e1 e2 = Shared $ do
                    hl <- unShared e1
                    hr <- unShared e2
                    recordC CAnd andMap (\s e -> s{ andMap = e}) (hl, hr)
    or  e1 e2 = Shared $ do
                    hl <- unShared e1
                    hr <- unShared e2
                    recordC COr orMap (\s e -> s{ orMap = e }) (hl, hr)
    not e = Shared $ do
                h <- unShared e
                recordC CNot notMap (\s e' -> s{ notMap = e' }) h
    xor l r = Shared $ do
                  hl <- unShared l ; hr <- unShared r
                  recordC CXor xorMap (\s e' -> s{ xorMap = e' }) (hl, hr)
    iff l r = Shared $ do
                  hl <- unShared l ; hr <- unShared r
                  recordC CIff iffMap (\s e' -> s{ iffMap = e' }) (hl, hr)
    onlyif l r = Shared $ do
                    hl <- unShared l ; hr <- unShared r
                    recordC COnlyif onlyifMap (\s e' -> s{ onlyifMap = e' }) (hl, hr)
    ite x t e = Shared $ do
        hx <- unShared x
        ht <- unShared t ; he <- unShared e
        recordC CIte iteMap (\s e' -> s{ iteMap = e' }) (hx, ht, he)

    eq xx yy = Shared $ do
                 x <- unShared xx
                 y <- unShared yy
                 recordC CEq eqMap (\s e -> s {eqMap = e}) (x,y)

    lt xx yy = Shared $ do
                 x <- unShared xx
                 y <- unShared yy
                 recordC CLt ltMap (\s e -> s {ltMap = e}) (x,y)

    nat = Shared . recordC CNat natMap (\s e -> s{ natMap = e })

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
             | TXor (Tree v) (Tree v)
             | TIff (Tree v) (Tree v)
             | TOnlyIf (Tree v) (Tree v)
             | TIte (Tree v) (Tree v) (Tree v)
             | TEq  (Tree v) (Tree v)
             | TLt  (Tree v) (Tree v)
             | TNat [v]
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
foldTree f i (TNat xx)    = foldr (flip f) i xx

instance Circuit Tree where
    true  = TTrue
    false = TFalse
    input = TLeaf
    and   = TAnd
    or    = TOr
    not   = TNot
    xor   = TXor
    iff   = TIff
    onlyif = TOnlyIf
    ite   = TIte
    eq    = TEq
    lt    = TLt
    nat   = TNat

instance CastCircuit Tree where
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
    castCircuit (TNat vv)    = nat vv

-- ** Circuit evaluator

type BEnv v = Map v Bool

-- | A circuit evaluator, that is, a circuit represented as a function from
-- variable values to booleans.
newtype Eval v = Eval { unEval :: BEnv v -> Either Integer Bool }

-- | Evaluate a circuit given inputs.
runEval :: BEnv v -> Eval v -> Either Integer Bool
runEval = flip unEval

instance Circuit Eval where
    true    = Eval $ const $ Right True
    false   = Eval $ const $ Right False
    input v = Eval $ \env -> Right $ 
                      Map.findWithDefault
                        (error $ "Eval: no such var: " ++ show v
                                 ++ " in " ++ show env)
                         v env
    and c1 c2 = Eval (\env -> Right $ fromRight(unEval c1 env) && fromRight(unEval c2 env))
    or  c1 c2 = Eval (\env -> Right $ fromRight(unEval c1 env) || fromRight(unEval c2 env))
    not c     = Eval (\env -> Right $ Prelude.not $ fromRight(unEval c env))
    eq c1 c2  = Eval (\env -> Right $ fromLeft(unEval c1 env) == fromLeft(unEval c2 env))
    lt c1 c2  = Eval (\env -> Right $ fromLeft(unEval c1 env) <  fromLeft(unEval c2 env))
    nat xx    = Eval (\env -> Left . fromBinary . map (fromRight . (`unEval` env) . input) $ xx)

fromBinary :: [ Bool ] -> Integer
fromBinary xs = foldr ( \ x y -> 2*y + if x then 1 else 0 ) 0 xs

fromLeft  :: Either l r -> l
fromRight :: Either l r -> r
fromLeft  =   either  id  (typeError "runEval: Expected a natural.")
fromRight = (`either` id) (typeError "runEval: Expected a boolean.")

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
                | NNat [v]
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

    eq     = binaryNode NEq
    lt     = binaryNode NLt
    nat xx = Graph $ do {n <- newNode; return (n, [(n, NNat xx)],[])}

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
simplifyTree   (TLt (TNat []) _) = TFalse
simplifyTree t@(TLt x y) = if x == y then TFalse else t
simplifyTree t@TNat{}    = t

-- ** Convert circuit to CNF

-- this data is private to toCNF.
data CNFResult = CP !Lit !(Set (Set Lit))
data CNFState = CNFS{ toCnfVars :: [Var]
                      -- ^ infinite fresh var source, starting at 1
                    , toCnfMap  :: Bimap Var CCode
                      -- ^ record var mapping
                    }
emptyCNFState :: CNFState
emptyCNFState = CNFS{ toCnfVars = [V 1 ..]
                    , toCnfMap = Bimap.empty }

-- retrieve and create (if necessary) a cnf variable for the given ccode.
--findVar :: (MonadState CNFState m) => CCode -> m Lit
findVar ccode = do
    m <- gets toCnfMap
    v:vs <- gets toCnfVars
    case Bimap.lookupR ccode m of
      Nothing -> do modify $ \s -> s{ toCnfMap = Bimap.insert v ccode m
                                    , toCnfVars = vs }
                    return . lit $ v
      Just v'  -> return . lit $ v'

-- | A circuit problem packages up the CNF corresponding to a given
-- `FrozenShared' circuit, and the mapping between the variables in the CNF and
-- the circuit elements of the circuit.
data CircuitProblem v = CircuitProblem
    { problemCnf :: CNF
    , problemCircuit :: FrozenShared v
    , problemCodeMap :: Bimap Var CCode }

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
toCNF cIn =
    let c@(FrozenShared sharedCircuit circuitMaps) =
            runShared . removeComplex $ cIn
        (cnf, m) = ((`runReader` circuitMaps) . (`runStateT` emptyCNFState)) $ do
                     (CP l theClauses) <- toCNF' sharedCircuit
                     return $ Set.insert (Set.singleton l) theClauses
    in CircuitProblem
       { problemCnf = CNF { numVars =   Set.fold max 1
                          . Set.map (Set.fold max 1)
                          . Set.map (Set.map (unVar . var))
                          $ cnf
                          , numClauses = Set.size cnf
                          , clauses = Set.map Foldable.toList cnf }
       , problemCircuit = c
       , problemCodeMap = toCnfMap m }
  where
    -- Returns (CP l c) where {l} U c is CNF equisatisfiable with the input
    -- circuit.  Note that CNF conversion only has cases for And, Or, Not, True,
    -- False, and Var circuits.  We therefore remove the complex circuit before
    -- passing stuff to this function.
    toCNF' c@(CVar{})   = do l <- findVar c
                             return (CP l Set.empty)
    toCNF' c@(CTrue{})  = do
        l <- findVar c
        return (CP l (Set.singleton . Set.singleton $ l))
    toCNF' c@(CFalse{}) = do
        l <- findVar c
        return (CP l (Set.fromList [Set.singleton (negate l)]))

--     -- x <-> -y
--     --   <-> (-x, -y) & (y, x)
    toCNF' c@(CNot i) = do
        notLit <- findVar c
        eTree <- extract i notMap
        (CP eLit eCnf) <- toCNF' eTree
        return
          (CP notLit
              (Set.fromList [ Set.fromList [negate notLit, negate eLit]
                         , Set.fromList [eLit, notLit] ]
              `Set.union` eCnf))

--     -- x <-> (y | z)
--     --   <-> (-y, x) & (-z, x) & (-x, y, z)
    toCNF' c@(COr i) = do
        orLit <- findVar c
        (l, r) <- extract i orMap
        (CP lLit lCnf) <- toCNF' l
        (CP rLit rCnf) <- toCNF' r
        return
          (CP orLit
              (Set.fromList [ Set.fromList [negate lLit, orLit]
                         , Set.fromList [negate rLit, orLit]
                         , Set.fromList [negate orLit, lLit, rLit] ]
              `Set.union` lCnf `Set.union` rCnf))
              
--     -- x <-> (y & z)
--     --   <-> (-x, y), (-x, z) & (-y, -z, x)
    toCNF' c@(CAnd i) = do
        andLit <- findVar c
        (l, r) <- extract i andMap
        (CP lLit lCnf) <- toCNF' l
        (CP rLit rCnf) <- toCNF' r
        return
          (CP andLit
             (Set.fromList [ Set.fromList [negate andLit, lLit]
                         , Set.fromList [negate andLit, rLit]
                         , Set.fromList [negate lLit, negate rLit, andLit] ]
             `Set.union` lCnf `Set.union` rCnf))

    toCNF' c = do
        m <- ask
        error $  "toCNF' bug: unknown code: " ++ show c
              ++ " with maps:\n" ++ show m


    extract code f = do
        m <- asks f
        case Bimap.lookup code m of
          Nothing -> error $ "toCNF: unknown code: " ++ show code
          Just x  -> return x

-- | Returns an equivalent circuit with no iff, xor, onlyif, ite, nat, eq and lt nodes.
removeComplex :: (Ord v, Show v, Circuit c) => FrozenShared v -> c v
removeComplex (FrozenShared code maps) = go code
  where
  go (CTrue{})  = true
  go (CFalse{}) = false
  go c@(CVar{}) = input $ getChildren c (varMap maps)
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
      | (x@CNat{}, y@CNat{}) <- getChildren c (eqMap maps)
      , xx <- getChildren x (natMap maps)
      , yy <- getChildren y (natMap maps)
      = eq xx yy

      | otherwise
      = typeError "removeComplex: expected a boolean."

  go c@(CLt{})
      | (x@CNat{}, y@CNat{}) <- getChildren c (ltMap maps)
      , xx <- getChildren x (natMap maps)
      , yy <- getChildren y (natMap maps)
      = lt xx yy

      | otherwise
      = typeError "removeComplex: expected a boolean."

  eq (p:pp) (q:qq) =      (     (not (input p) `and` not (input q))
                           `or` (input p `and` input q)
                          )
                     `and` eq pp qq
  eq [] [] = true
  eq [] qq = not $ foldl' or false $ map input qq
  eq pp [] = not $ foldl' or false $ map input pp

  lt (p:pp) (q:qq) = lt pp qq `or` (not (input p) `and` input q `and` eq pp qq)
  lt [] qq = foldl' or false $ map input qq
  lt _  [] = false


onTup :: (a -> b) -> (a, a) -> (b, b)
onTup f (x, y) = (f x, f y)

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

typeError :: String -> a
typeError msg = error (msg ++ "\nPlease send an email to the pepeiborra@gmail.com requesting a typed circuit language.")
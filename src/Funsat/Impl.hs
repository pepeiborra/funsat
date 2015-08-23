{-# LANGUAGE BangPatterns #-}
module Funsat.Impl where

import Control.Applicative
import Data.Foldable
import Funsat.ECircuit
import Funsat.Types


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
             | TFromInteger Integer
             | TAdd (Tree v) (Tree v)
             | TSubstract (Tree v) (Tree v)
             | TNeg (Tree v)
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

instance (ECircuit c) => CastCircuit Tree c where
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

instance Num Eval where
    eq c1 c2  = Eval (\env -> Right $ fromLeft(unEval c1 env) == fromLeft(unEval c2 env))
    lt c1 c2  = Eval (\env -> Right $ fromLeft(unEval c1 env) <  fromLeft(unEval c2 env))
    nat v     = Eval (\env -> Map.findWithDefault (Left (0 :: Int))
--                                     (error $ "Eval: no such nat: " ++ show v
  --                                         ++ " in " ++ show env)
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
    go c@(CExistBool i) = return (i, [(i, frz c)], [])
    go c@(CExistNat  i) = return (i, [(i, frz c)], [])
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
    go c@(CExistBool i) = return (i, [(i, frz c)], [])
    go c@(CExistNat  i) = return (i, [(i, frz c)], [])
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
    frz (CExistBool i) = "?" ++ show i ++ "(bool)"
    frz (CExistNat  i) = "?" ++ show i ++ "(nat)"
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
    go c@CExistBool{} = findVar' c goOn goOn
    go c@CExistNat{}  = findVar' c goOn goOn
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
  go' c@CExistBool{} = return c
  go' c@CExistNat{}  = return c
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
  go   CExistBool{} = existsBool id
  go   CExistNat{}  = existsNat  id
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

{-# LANGUAGE MultiParamTypeClasses
            ,FunctionalDependencies
            ,FlexibleInstances
            ,FlexibleContexts
            ,GeneralizedNewtypeDeriving
            ,TypeSynonymInstances
            ,TypeOperators
            ,ParallelListComp
            ,BangPatterns
 #-}

{-
    This file is part of funsat.

    funsat is free software: it is released under the BSD3 open source license.
    You can find details of this license in the file LICENSE at the root of the
    source tree.

    Copyright 2008 Denis Bueno
-}



-- | Data types used when dealing with SAT problems in funsat.
module Funsat.Types where


import Data.Array.Unboxed
import Data.Foldable hiding ( sequence_ )
import Data.List( intercalate )
import Prelude hiding ( sum, concatMap, elem, foldr, foldl, any, maximum )

-- * Basic Types

newtype Var = V {unVar :: Int} deriving (Eq, Ord, Enum, Ix)

instance Show Var where
    show (V i) = show i ++ "v"

instance Num Var where
    _ + _ = error "+ doesn't make sense for variables"
    _ - _ = error "- doesn't make sense for variables"
    _ * _ = error "* doesn't make sense for variables"
    signum _ = error "signum doesn't make sense for variables"
    negate = error "negate doesn't make sense for variables"
    abs = id
    fromInteger l | l <= 0    = error $ show l ++ " is not a variable"
                  | otherwise = V $ fromInteger l

newtype Lit = L {unLit :: Int} deriving (Eq, Ord, Enum, Ix)

instance Num Lit where
    _ + _ = error "+ doesn't make sense for literals"
    _ - _ = error "- doesn't make sense for literals"
    _ * _ = error "* doesn't make sense for literals"
    signum _ = error "signum doesn't make sense for literals"
    negate   = inLit negate
    abs      = inLit abs
    fromInteger l | l == 0    = error "0 is not a literal"
                  | otherwise = L $ fromInteger l

-- | Transform the number inside the literal.
inLit :: (Int -> Int) -> Lit -> Lit
inLit f = L . f . unLit

-- | The polarity of the literal.  Negative literals are false; positive
-- literals are true.  The 0-literal is an error.
litSign :: Lit -> Bool
litSign (L x) | x < 0     = False
              | x > 0     = True
              | otherwise = error "litSign of 0"

instance Show Lit where show = show . unLit
instance Read Lit where
    readsPrec i s = map (\(i,s) -> (L i, s)) (readsPrec i s)

-- | The variable for the given literal.
var :: Lit -> Var
var = V . abs . unLit

-- | The positive literal for the given variable.
lit :: Var -> Lit
lit = L . unVar

type Clause = [Lit]

data CNF = CNF
    { numVars    :: Int
    , numClauses :: Int
    , clauses    :: [Clause] } deriving (Show, Read, Eq)

-- | The solution to a SAT problem.  In each case we return an assignment,
-- which is obviously right in the `Sat' case; in the `Unsat' case, the reason
-- is to assist in the generation of an unsatisfiable core.
data Solution = Sat !IAssignment | Unsat !IAssignment deriving (Eq)

instance Show Solution where
   show (Sat a)     = "satisfiable: " ++ showAssignment a
   show (Unsat _)   = "unsatisfiable"

finalAssignment :: Solution -> IAssignment
finalAssignment (Sat a)   = a
finalAssignment (Unsat a) = a

-- * Assignments


-- | An ''immutable assignment''.  Stores the current assignment according to
-- the following convention.  A literal @L i@ is in the assignment if in
-- location @(abs i)@ in the array, @i@ is present.  Literal @L i@ is absent
-- if in location @(abs i)@ there is 0.  It is an error if the location @(abs
-- i)@ is any value other than @0@ or @i@ or @negate i@.
--
-- Note that the `Model' instance for `Lit' and `IAssignment' takes constant
-- time to execute because of this representation for assignments.  Also
-- updating an assignment with newly-assigned literals takes constant time,
-- and can be done destructively, but safely.
type IAssignment = UArray Var Int

showAssignment :: IAssignment -> String
showAssignment a = intercalate " " ([show (a!i) | i <- range . bounds $ a,
                                                  (a!i) /= 0])


-- | The assignment as a list of signed literals.
litAssignment :: IAssignment -> [Lit]
litAssignment mFr = foldr (\i ass -> if mFr!i == 0 then ass
                                     else (L . (mFr!) $ i) : ass)
                          []
                          (range . bounds $ mFr)

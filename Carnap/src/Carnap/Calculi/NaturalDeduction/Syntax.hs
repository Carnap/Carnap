{-#LANGUAGE GADTs, KindSignatures, TypeOperators, FlexibleContexts, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, UndecidableInstances, FunctionalDependencies, RankNTypes, ConstraintKinds #-}
module Carnap.Calculi.NaturalDeduction.Syntax where

import Data.Tree
import Data.Map (Map)
import Data.IORef (IORef)
import Data.List (permutations, (\\))
import Data.Hashable
import Data.Typeable
import Control.Lens
import Carnap.Core.Unification.Unification
--import Carnap.Core.Unification.FirstOrder
import Carnap.Core.Unification.ACUI
import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes
import Carnap.Core.Data.Optics
import Carnap.Calculi.Util
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.Util.LanguageClasses
import Control.Monad.State
import Text.Parsec (Parsec, ParseError)

--------------------------------------------------------
--1. Data For Natural Deduction
--------------------------------------------------------

---------------------------
--  1.0 Deduction Lines  --
---------------------------

type MultiRule r = [r]

data DeductionLine r lex a where
        AssertLine :: 
            { asserted :: FixLang lex a
            , assertRule :: MultiRule r
            , assertDepth :: Int
            , assertDependencies :: [(Int,Int)]
            } -> DeductionLine r lex a
        DependentAssertLine ::
            { dependAsserted :: FixLang lex a
            , dependAssertRule :: MultiRule r
            , dependAssertDependencies :: [(Int,Int)]
            , dependAssertDischarged :: Maybe [Int]
            , dependAssertInScope:: [Int]
            , dependAssertLineNo:: Maybe Int
            } -> DeductionLine r lex a
        ShowLine :: 
            { toShow :: FixLang lex a
            , showDepth :: Int
            } -> DeductionLine r lex a
        ShowWithLine :: 
            { toShowWith :: FixLang lex a
            , showWithDepth :: Int
            , showWithRule :: MultiRule r
            , showWithDependencies :: [(Int,Int)]
            } -> DeductionLine r lex a
        QedLine :: 
            { closureRule :: MultiRule r
            , closureDepth :: Int
            , closureDependencies :: [(Int,Int)]
            } -> DeductionLine r lex a
        PartialLine ::
            { partialLineContent :: Either String (FixLang lex a)
            , partialLineError   :: ParseError
            , partialLineDepth   :: Int
            } -> DeductionLine r lex a
        SeparatorLine ::
            { separatorLineDepth :: Int
            } -> DeductionLine r lex a

ruleOfLine (AssertLine _ r _ _) = Just r
ruleOfLine (DependentAssertLine _ r _ _ _ _) = Just r
ruleOfLine (ShowWithLine _ _ r _) = Just r
ruleOfLine (QedLine r _ _) = Just r
ruleOfLine _ = Nothing

depth (AssertLine _ _ dpth _) = dpth
depth (DependentAssertLine _ _ _ _ _ _) = 0
depth (ShowLine _ dpth) = dpth
depth (ShowWithLine _ dpth _ _) = dpth
depth (QedLine _ dpth _) = dpth
depth (PartialLine _ _ dpth) = dpth
depth (SeparatorLine dpth) = dpth

dependencies (AssertLine _ _ _ deps) = Just deps
dependencies (DependentAssertLine _ _ deps _ _ _) = Just deps
dependencies _ = Nothing

assertion (AssertLine f _ _ _) = Just f
assertion (DependentAssertLine f _ _ _ _ _) = Just f
assertion (ShowLine f _) = Just f
assertion (ShowWithLine f _ _ _) = Just f
assertion _ = Nothing

isAssumptionLine :: Inference r lex sem => DeductionLine r lex sem -> Bool
isAssumptionLine (AssertLine _ r _ _) = or (map isAssumption r)
isAssumptionLine (DependentAssertLine _ r _ _ _ _) = or (map isAssumption r)
isAssumptionLine _ = False

isOnlyAssumptionLine :: Inference r lex sem => DeductionLine r lex sem -> Bool
isOnlyAssumptionLine (AssertLine _ r _ _) = and (map isAssumption r)
isOnlyAssumptionLine (DependentAssertLine _ r _ _ _ _) = and (map isAssumption r)
isOnlyAssumptionLine _ = False

isPremiseLine :: Inference r lex sem => DeductionLine r lex sem -> Bool
isPremiseLine (AssertLine _ r _ _) = and (map isPremise r)
isPremiseLine (DependentAssertLine _ r _ _ _ _) = and (map isPremise r)
isPremiseLine _ = False

inScope (DependentAssertLine _ _ _ _ s _) = s
inScope _ = []

discharged (DependentAssertLine _ _ _ (Just d) _ _) = d
discharged _ = []

justificationOf (AssertLine _ r _ _) = Just r 
justificationOf (DependentAssertLine _ r _ _ _ _) = Just r
justificationOf _ = Nothing

----------------------
--  1.1 Deductions  --
----------------------

type Deduction r lex sem = [DeductionLine r lex sem]

---------------------------
--  1.2 Deduction Trees  --
---------------------------

--Deduction trees are deduction lines organized in a treelike structure
--indicating subproofs. They are not assumed to include every line; so for
--example, the lines available from a given line may be regarded as
--a deduction tree.
data DeductionTree r lex sem = Leaf Int (DeductionLine r lex sem) 
                         | SubProof (Int,Int) [DeductionTree r lex sem]
                         --
--First and last numbers of a given deduction tree
headNum (Leaf n _) = n
headNum (SubProof (n,_) _) = n

--First and last numbers of a given deduction tree
tailNum (Leaf n _) = n
tailNum (SubProof (_,n) _) = n

--one step of getting the deduction tree where a certian line resides
locale m l@(Leaf n _) = if n == m then Just l else Nothing
locale _ (SubProof _ []) = Nothing
locale k (SubProof (n,m) (l:ls)) | k < n = Nothing
                                 | k <= tailNum l = Just l
                                 | otherwise = locale k (SubProof (n,m) ls)

--getting a line by number

(.!) :: DeductionTree r lex sem -> Int -> Maybe (DeductionLine r lex sem)
(Leaf n l) .! m = if n == m then Just l else Nothing
sp .! m = case locale m sp of
              Just sp' -> sp' .! m
              Nothing -> Nothing

--getting the surrounding subproof of a line, if there is one
subProofOf m (Leaf n l)  = Nothing
subProofOf m sp = case locale m sp of 
              Just (Leaf _ _) -> Just sp
              Just sp' -> subProofOf m sp'
              Nothing -> Nothing

--getting the subproof in a certain range, if there is one
range _ _ l@(Leaf _ _) = Nothing
range i j sp@(SubProof (n,m) ls) = if n == i && j == m then Just sp
                                                       else locale i sp >>= range i j

--getting the subtree of available lines for a given line (which is assumed
--to be contained in the given deduction tree)
availableLine m l@(Leaf n _) = if n == m then Just l else Nothing
availableLine m sp@(SubProof r ls) = do loc <- locale m sp
                                        recur <- availableLine m loc
                                        return $ SubProof r $ preleaves ++ [recur] ++ postleaves
    where clean = filter (\x -> case x of SubProof _ _ -> False; _ -> True) ls
          preleaves = filter (\(Leaf x _) -> x < m) clean
          postleaves = filter (\(Leaf x _) -> x < m) clean

--getting the subtree of available subproofs for a given line (which is assumed
--to be contained in the given deduction tree)
availableSubproof m l@(Leaf _ _) = Nothing
availableSubproof m sp@(SubProof r ls) = do loc <- locale m sp
                                            case loc of
                                                (Leaf _ _) -> return $ SubProof r $ preproofs ++ postproofs
                                                _ -> do recur <- availableSubproof m loc
                                                        return $ SubProof r $ preproofs ++ [recur] ++ postproofs
                                                
    where clean = filter (\x -> case x of SubProof _ _ -> True; _ -> False) ls
          removeChildren (SubProof r _) = SubProof r []
          preproofs = map removeChildren . filter (\(SubProof (_,n) _) -> n < m) $ clean
          postproofs = map removeChildren . filter (\(SubProof (n,_) _) -> n < m) $ clean

--------------------------
--  1.3 Error Messages  --
--------------------------

------------------
--  1.3 Proofs  --
------------------

data ProofLine r lex sem where 
       ProofLine :: Inference r lex sem => 
            { lineNo  :: Int 
            , content :: ClassicalSequentOver lex (Succedent sem)
            , rule    :: [r] } -> ProofLine r lex sem

instance (Eq r, Eq (ClassicalSequentOver lex (Succedent sem))) => Eq (ProofLine r lex sem)
        where (ProofLine n c r) == (ProofLine n' c' r') = n == n' && c == c' && r == r'

instance (Ord r, Ord (ClassicalSequentOver lex (Succedent sem))) => Ord (ProofLine r lex sem)
        where (ProofLine n c r) < (ProofLine n' c' r') =  n < n' 
                                                       || (n == n' && c < c')
                                                       || (n == n' && c == c' && r < r')

instance (Show (ClassicalSequentOver lex (Succedent sem)), Show r) => Hashable (ProofLine r lex sem)
        where hashWithSalt k (ProofLine n l r) = hashWithSalt k n 
                                                 `hashWithSalt` show l 
                                                 `hashWithSalt` show r

type ProofTree r lex sem = Tree (ProofLine r lex sem)

instance Ord a => Ord (Tree a) where 
        compare (Node x ts) (Node x' ts') = case compare x x' of
                                                EQ -> compare ts ts'
                                                c -> c

instance Hashable a => Hashable (Tree a) where 
        hashWithSalt k (Node x ts) = hashWithSalt k x `hashWithSalt` ts

--------------------
--  1.4 Feedback  --
--------------------

type FeedbackLine lex sem = Either (ProofErrorMessage lex) (ClassicalSequentOver lex (Sequent sem))

data Feedback lex sem = Feedback { finalresult :: Maybe (ClassicalSequentOver lex (Sequent sem))
                             , lineresults :: [FeedbackLine lex sem]}

type SequentTree lex sem = Tree (Int, ClassicalSequentOver lex (Sequent sem))

--Proof skeletons: trees of schematic sequences generated by a tree of
--inference rules. 

-------------------
--  1.5 Calculi  --
-------------------
--These are intended to wrap up a whole ND system, including some of its
--superficial features like rendering.

data RenderStyle = MontagueStyle | FitchStyle FitchVariant | LemmonStyle LemmonVariant | NoRender

data LemmonVariant = StandardLemmon | TomassiStyle

data FitchVariant = StandardFitch | BergmanMooreAndNelsonStyle

type ProofMemoRef lex sem r = IORef (Map Int [Either (ProofErrorMessage lex) 
                                                     [(ClassicalSequentOver lex (Sequent sem)
                                                     , [Equation (ClassicalSequentOver lex)]
                                                     , r)]
                                           ])

data RuntimeNaturalDeductionConfig lex sem = RuntimeNaturalDeductionConfig
        { derivedRules :: Map String (ClassicalSequentOver lex (Sequent sem))
        , problemPremises :: Maybe [ClassicalSequentOver lex (Sequent sem)]
        }

data NaturalDeductionCalc r lex sem = NaturalDeductionCalc 
        { ndRenderer :: RenderStyle
        , ndParseProof :: RuntimeNaturalDeductionConfig lex sem
                            -> String -> [DeductionLine r lex sem]
        , ndProcessLine :: (Sequentable lex , Inference r lex sem, MonadVar (ClassicalSequentOver lex) (State Int))
                                => Deduction r lex sem -> Restrictor r lex -> Int -> FeedbackLine lex sem
        , ndProcessLineMemo :: (Sequentable lex , Inference r lex sem, MonadVar (ClassicalSequentOver lex) (State Int))
                                => Maybe (ProofMemoRef lex sem r -> Deduction r lex sem -> Restrictor r lex -> Int -> IO (FeedbackLine lex sem))
        , ndParseSeq :: (Sequentable lex, Typeable sem,  ParsableLex sem lex) => Parsec String () (ClassicalSequentOver lex (Sequent sem))
        , ndParseForm :: ParsableLex sem lex => Parsec String () (FixLang lex sem)
        , ndNotation :: String -> String
        }

mkNDCalc :: NaturalDeductionCalc r lex sem
mkNDCalc = NaturalDeductionCalc 
    { ndRenderer = NoRender
    , ndProcessLineMemo = Nothing
    , ndNotation = id
    , ndParseForm = langParser
    , ndParseSeq = parseSeqOver langParser
    }

--------------------------------------------------------
--2. Typeclasses for natural deduction
--------------------------------------------------------

data ProofType = ProofType 
               { assumptionNumber :: Int 
               --the number of initial lines which must be assumptions (in some proof systems, used as premises for explicit indirect rules)
               , conclusionNumber :: Int 
               --the number of final available lines that figure in the rule (in some proof systems, used as premises)
               } --any remaining premises need to be gathered explicitly

data IndirectArity = PolyProof --takes an arbitrary number of assertions or subproofs, each ending in one assertion
                   | TypedProof ProofType --takes a subproof with a particular structure, given by a prooftype
                   | ImplicitProof ProofType --takes a subproof which is not cited explicitly, as in Gamut
                   | PolyTypedProof Int (ProofType) --takes n subproofs, each with the structure given by prooftype
                   | WithAlternate IndirectArity IndirectArity --tries the first, and on failure, falls back on the second
                   | DeferTo Int --looks to some other line to determine proof type
                   | DeferredTo IndirectArity --is targeted by a deferal

doubleProof = TypedProof (ProofType 0 2)

assumptiveProof = TypedProof (ProofType 1 1)

type Restrictor r lex = Int -> r -> Maybe (Restriction lex)

andFurtherRestriction f g sub = case f sub of 
                                  Nothing -> g sub
                                  Just e  -> Just e

class Inference r lex sem | r -> lex sem where

        premisesOf :: r -> [ClassicalSequentOver lex (Sequent sem)]
        premisesOf r = upperSequents (ruleOf r)

        conclusionOf :: r -> ClassicalSequentOver lex (Sequent sem)
        conclusionOf r = lowerSequent (ruleOf r)

        ruleOf :: r -> SequentRule lex sem
        ruleOf r = SequentRule (premisesOf r) (conclusionOf r)

        --local restrictions, based only on given substitutions
        restriction :: r -> Maybe (Restriction lex)
        restriction _ = Nothing

        --restrictions, based on given substitutions, whole derivation, and position in derivation
        --XXX: the either here is a bit of a hack
        globalRestriction :: Either (Deduction r lex sem) (DeductionTree r lex sem) -> Restrictor r lex
        globalRestriction _ _ _ = Nothing
        
        indirectInference :: r -> Maybe IndirectArity
        indirectInference = const Nothing

        isAssumption :: r -> Bool
        isAssumption = const False
        
        isPremise :: r -> Bool
        isPremise = const False
        --TODO: template for error messages, etc.

class StructuralInference rule lex struct where
        structuralRestriction :: struct -> Restrictor rule lex
        structuralRestriction _ _ _ = Nothing

class StructuralOverride rule struct where
        structuralOverride :: struct -> rule -> Maybe [rule]
        structuralOverride _ _ = Nothing

class AssumptionNumbers r where
        introducesAssumptions :: r -> [Int]
        dischargesAssumptions :: r -> [Int]

leavesLabeled :: AssumptionNumbers rule => Int -> ProofTree rule lex sem -> [ProofTree rule lex sem]
leavesLabeled n pt = filter (\(Node pl _) -> introducesAssumptions (head (rule pl)) == [n]) $ toListOf leaves pt

usesAssumptions n pt assumps sub | leaves == [] = Just "This inference seems to be citing an assumption that doesn't exist"
                                 | not (all test leaves) = Just "A cited assumption doesn't have the right form for this rule."
                                 | otherwise = Nothing
    where assumps' = map (pureBNF . applySub sub) assumps
          test (Node x _) = content x `elem` assumps'
          leaves = leavesLabeled n pt

usesAssumption n pt assump = usesAssumptions n pt [assump]

exhaustsAssumptions n pt assump sub = if all (`elem` dischargedList pt) assumpInstances 
                                          then Nothing
                                          else Just "There's an assumption above that needs to be cited before this rule can discharge it."
    where dischargedList (Node r f) = dischargesAssumptions (head (rule r)) ++ concatMap dischargedList f
          theAssump = pureBNF (applySub sub assump)
          assumpInstances = concatMap (\(Node pl _) -> case rule pl of [r] -> introducesAssumptions r; _ -> [])
                          . filter (\(Node pl _) -> content pl == theAssump) 
                          $ toListOf leaves pt

--Makes sure that all the cited assumptions have the form that we get by
--applying the substitution generated by the inference to `assump`
checkAssumptionForm n pt assump sub = 
        case leavesLabeled n pt of
            [] -> Nothing
            (Node x _ : rest) -> case subsfrom (content x) of
                Left e -> Just $ "The asssumption cited, namely " ++ show (content x) ++ ", does not have the right form, namely " ++ show assump'
                Right (sub':_) | any (differentContent x) rest -> Just "the cited assumptions don't all have the same form"
                               | otherwise -> Nothing
    where subsfrom form = hosolve [assump' :=: form]
          assump' = pureBNF $ applySub sub (SS assump)
          differentContent x (Node y _) = content x /= content y

type SupportsND r lex sem = 
    ( Show r 
    , Typeable sem
    , ReLex lex 
    , Inference r lex sem
    , Schematizable (lex (FixLang lex))
    , Schematizable (lex (ClassicalSequentOver lex))
    , PrismLink (lex (FixLang lex)) (SubstitutionalVariable (FixLang lex))
    , PrismLink (lex (ClassicalSequentOver lex)) (SubstitutionalVariable (ClassicalSequentOver lex))
    , FirstOrderLex (lex (FixLang lex))
    , FirstOrderLex (lex (ClassicalSequentOver lex))
    , ParsableLex sem lex
    , CopulaSchema (FixLang lex)
    , CopulaSchema (ClassicalSequentOver lex)
    )

--------------------------------------------------------
--2. Transformations
--------------------------------------------------------

--Proof Tree to Sequent Tree
--
-- Proof Tree to proof skeleton)

-----------------
--  3. Optics  --
-----------------

leaves :: Traversal' (Tree a) (Tree a)
leaves f (Node x []) = f (Node x [])
leaves f (Node x xs) = Node <$> pure x <*> traverse (leaves f) xs

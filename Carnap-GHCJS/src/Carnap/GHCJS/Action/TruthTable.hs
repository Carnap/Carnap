{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module Carnap.GHCJS.Action.TruthTable (truthTableAction) where

import Lib
import Carnap.GHCJS.SharedTypes
import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes (Schematizable, Modelable(..))
import Carnap.Calculi.NaturalDeduction.Syntax (NaturalDeductionCalc(..))
import Carnap.Languages.PurePropositional.Syntax (PurePropLexicon)
import Carnap.Languages.PurePropositional.Logic
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Util (getIndicies)
import Carnap.Languages.PurePropositional.Syntax (PureForm)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.PurePropositional.Logic (PropSequentCalc)
import Carnap.Languages.Util.LanguageClasses
import GHCJS.DOM.Types
import GHCJS.DOM.Element
import GHCJS.DOM.HTMLSelectElement (castToHTMLSelectElement, getValue) 
import GHCJS.DOM.Window (alert, prompt)
import GHCJS.DOM.Document (createElement, getDefaultView)
import GHCJS.DOM.Node (appendChild, getParentNode, insertBefore)
import GHCJS.DOM.EventM (newListener, addListener, EventM, target)
import Data.IORef (newIORef, IORef, readIORef,writeIORef, modifyIORef)
import Data.Map as M (Map, lookup, foldr, insert, fromList, toList)
import Data.Text (pack)
import Data.Either (rights)
import Data.List (subsequences, intercalate, nub, zip4, intersperse)
import Control.Monad.IO.Class (liftIO)
import Control.Lens (toListOf, preview)
import Control.Lens.Plated (children)
import Text.Parsec (parse, spaces, sepEndBy1, char, eof, optional, try, (<|>))

truthTableAction :: IO ()
truthTableAction = initElements getTruthTables activateTruthTables

getTruthTables :: Document -> HTMLElement -> IO [Maybe (Element, Element, Map String String)]
getTruthTables d = genInOutElts d "div" "div" "truthtable"

activateTruthTables :: Document -> Maybe (Element, Element, Map String String) -> IO ()
activateTruthTables w (Just (i,o,opts)) = do
        case M.lookup "tabletype" opts of
            Just "simple" -> checkerWith (formListParser <* eof) createSimpleTruthTable
            Just "validity" -> checkerWith seqParser createValidityTruthTable
            Just "partial" -> checkerWith (formListPairParser <* eof) createPartialTruthTable
            _  -> return ()

    where (formParser,seqParser) = case M.lookup "system" opts >>= \sys -> (,) <$> ndParseForm `ofPropSys` sys <*> ndParseSeq `ofPropSys` sys of
                                         Just pair -> pair
                                         Nothing -> (purePropFormulaParser standardLetters, ndParseSeq montagueSCCalc)
          formListParser = formParser `sepEndBy1` (spaces *> char ',' <* spaces)
          formListPairParser = do gs <- try (formListParser <* char ':') <|> return []
                                  optional (char ':')
                                  spaces
                                  fs <- formListParser
                                  return (gs,fs)
          
          checkerWith parser ttbuilder = 
            case M.lookup "goal" opts of
                Just g ->
                  case parse parser "" g of
                      Left e -> setInnerHTML o (Just $ show e) 
                      Right f -> do
                          ref <- newIORef False
                          bw <- buttonWrapper w
                          (check,rows) <- ttbuilder w f (i,o) ref bw opts
                          case M.lookup "submission" opts of
                              Just s | take 7 s == "saveAs:" -> do
                                  let l = Prelude.drop 7 s
                                  bt1 <- doneButton w "Submit"
                                  appendChild bw (Just bt1)
                                  submit <- newListener $ submitTruthTable opts ref check rows (show f) l
                                  addListener bt1 click submit False                
                              _ -> return ()
                          if "nocheck" `inOpts` opts then return () 
                          else do
                              bt2 <- questionButton w "Check"
                              appendChild bw (Just bt2)
                              checkIt <- newListener $ checkTable ref check
                              addListener bt2 click checkIt False                
                          Just par <- getParentNode o
                          appendChild par (Just bw)
                          return ()
                _ -> print "truth table was missing an option"
          checkTable ref check = do correct <- liftIO $ check
                                    if correct 
                                        then do message "Success!"
                                                liftIO $ writeIORef ref True
                                                setAttribute i "class" "input completeTT"
                                        else do message "Something's not quite right"
                                                liftIO $ writeIORef ref False
                                                setAttribute i "class" "input incompleteTT"

submitTruthTable:: Map String String -> IORef Bool ->  IO Bool -> [Element] -> String -> String -> EventM HTMLInputElement e ()
submitTruthTable opts ref check rows s l = do isDone <- liftIO $ readIORef ref
                                              if isDone 
                                                 then trySubmit TruthTable opts l (ProblemContent (pack s)) True
                                                 else if "exam" `inOpts` opts
                                                          then do correct <- liftIO check
                                                                  if correct
                                                                      then trySubmit TruthTable opts l (ProblemContent (pack s)) True
                                                                      else do tabulated <- liftIO $ mapM unpackRow rows
                                                                              trySubmit TruthTable opts l (TruthTableDataOpts (pack s) (reverse tabulated) (M.toList opts)) False
                                                          else message "not yet finished (do you still need to check your answer?)"

-------------------------
--  Full Truth Tables  --
-------------------------

createValidityTruthTable :: Document -> PropSequentCalc (Sequent (Form Bool)) 
    -> (Element,Element) -> IORef Bool -> Element -> Map String String
    -> IO (IO Bool, [Element])
createValidityTruthTable w (antced :|-: succed) (i,o) ref bw opts =
        do setInnerHTML i (Just . rewriteWith opts . show $ (antced :|-: succed))
           admissibleRows <- case M.lookup "counterexample-to" opts of
                               Just "equivalence" -> do 
                                    addCounterexample w opts bw i ref atomIndicies isEquivCE "Inequivalent"
                                    return $ map (Just . not . isEquivCE) valuations
                               Just "inconsistency" -> do 
                                    addCounterexample w opts bw i ref atomIndicies isInconCE "Consistent"
                                    return $ map (Just . not . isInconCE) valuations
                               Just "validity" -> do 
                                    addCounterexample w opts bw i ref atomIndicies isValCE "Invalid"
                                    return $ map (Just . not . isValCE) valuations
                               _ -> do 
                                    addCounterexample w opts bw i ref atomIndicies isValCE "Counterexample"
                                    return $ map (Just . not . isValCE) valuations
           assembleTable w opts o orderedChildren valuations atomIndicies admissibleRows

    where forms = antecedList ++ succedList
          antecedList = map fromSequent $ toListOf concretes antced
          succedList = map fromSequent $ toListOf concretes succed
          isValCE v = and (map (unform . satisfies v) antecedList ) 
                   && and (map (not . unform . satisfies v) succedList)
          isEquivCE v = and (map (unform . satisfies v) antecedList) 
                     && not (and succVals || and (map not succVals))
            where succVals = map (unform . satisfies v) succedList
          isInconCE v = and (map (unform . satisfies v) antecedList)
                     && and (map (unform . satisfies v) succedList)
          atomIndicies = nub . sort . concatMap getIndicies $ forms
          valuations = map toValuation . subsequences $ reverse atomIndicies
          orderedChildren = concat $ intersperse [Left ','] (map (toOrderedChildren . fromSequent) (toListOf concretes antced))
                                  ++ [[Left '⊢']] 
                                  ++ intersperse [Left ','] (map (toOrderedChildren. fromSequent) (toListOf concretes succed))

createSimpleTruthTable :: Document -> [PureForm] -> (Element,Element) -> IORef Bool 
    -> Element -> Map String String 
    -> IO (IO Bool,[Element])
createSimpleTruthTable w fs (i,o) ref bw opts = 
        do setInnerHTML i (Just . intercalate ", " . map (rewriteWith opts . show) $ fs)
           case M.lookup "counterexample-to" opts of
                Just "equivalence" -> addCounterexample w opts bw i ref atomIndicies isEquivCE "Inequivalent"
                Just "inconsistency" -> addCounterexample w opts bw i ref atomIndicies isInconCE "Consistent"
                Just "tautology" -> addCounterexample w opts bw i ref atomIndicies isTautCE "Non-Tautology"
                Just "validity" -> addCounterexample w opts bw i ref atomIndicies isTautCE "Invalid"
                _ -> do addCounterexample w opts bw i ref atomIndicies isTautCE "Counterexample"
           assembleTable w opts o orderedChildren valuations atomIndicies (repeat Nothing)

    where isTautCE v = and (map (not . unform . satisfies v) fs)
          isEquivCE v = not (and vals || and (map not vals))
            where vals = map (not . unform . satisfies v) fs
          isInconCE v = and (map (unform . satisfies v) fs)
          atomIndicies = nub . sort . concatMap getIndicies $ fs
          valuations = map toValuation . subsequences $ reverse atomIndicies
          orderedChildren = concat . intersperse [Left ','] . map toOrderedChildren $ fs

assembleTable :: Document -> Map String String -> Element -> [Either Char PureForm] 
    -> [Int -> Bool] -> [Int] -> [Maybe Bool]
    -> IO (IO Bool, [Element])
assembleTable w opts o orderedChildren valuations atomIndicies admissibleRows = 
        do (table, thead, tbody) <- initTable w          
           gridRef <- makeGridRef (length orderedChildren) (length valuations)
           head <- toHead w opts atomIndicies orderedChildren
           rows <- mapM (toRow' gridRef) (zip4 valuations [1..] admissibleRows givens)
           mapM_ (appendChild tbody . Just) (reverse rows)
           appendChild thead (Just head)
           appendChild o (Just table)
           let check = M.foldr (&&) True <$> readIORef gridRef 
           return (check,rows)
    where toRow' = toRow w opts atomIndicies orderedChildren
          givens = makeGivens opts (Just $ length valuations) orderedChildren

addCounterexample :: Document -> Map String String ->  Element -> Element 
    -> IORef Bool -> [Int] -> ((Int -> Bool) -> Bool) -> String
    -> IO ()
addCounterexample w opts bw i ref atomIndicies isCounterexample title
    | "nocounterexample" `inOpts` opts = return ()
    | otherwise = do bt <- exclaimButton w title
                     Just w' <- getDefaultView w                    
                     counterexample <- newListener $ liftIO $ tryCounterexample w' opts ref i atomIndicies isCounterexample
                     addListener bt click counterexample False
                     appendChild bw (Just bt)
                     return ()

tryCounterexample :: Window -> Map String String -> IORef Bool -> Element 
    -> [Int] -> ((Int -> Bool) -> Bool) 
    -> IO ()
tryCounterexample w opts ref i indicies isCounterexample = 
        do mrow <- prompt w "enter the truth values for your counterexample row" (Just "")
           case mrow of 
               Nothing -> return ()
               Just s -> 
                   case checkLength =<< (clean $ map charToTruthValue s) of
                     Nothing -> alert w "not a readable row"
                     Just l -> do let v = listToVal l
                                  let s = isCounterexample v
                                  if "exam" `inOpts` opts 
                                      then do alert w "Counterexample received - If you're confident that it is correct, press Submit to submit it."
                                              writeIORef ref s
                                      else if s then 
                                           do alert w "Success!"
                                              writeIORef ref True
                                              setAttribute i "class" "input completeTT"
                                      else do alert w "Something's not quite right"
                                              writeIORef ref False
                                              setAttribute i "class" "input incompleteTT"
        where clean (Nothing:xs) = Nothing
              clean (Just x:xs) = (:) <$> (Just x) <*> (clean xs)
              clean [] = Just []
              listToVal l = toValuation (mask l indicies)
              mask (x:xs) (y:ys) = if x then y:(mask xs ys) else mask xs ys
              mask [] _ = []
              checkLength l = if length l == length indicies then Just l else Nothing

toRow :: Document -> Map String String -> [Int] 
    -> [Either Char PureForm] -> IORef (Map (Int,Int) Bool) 
    -> (Int -> Bool, Int, Maybe Bool, [Maybe Bool])
    -> IO Element
toRow w opts atomIndicies orderedChildren gridRef (v,n,mvalid,given) = 
        do Just row <- createElement w (Just "tr")
           Just sep <- createElement w (Just "td")
           setAttribute sep "class" "tttdSep"
           valTds <- mapM toValTd atomIndicies
           childTds <- mapM toChildTd (zip3 orderedChildren [1..] given)
           mapM_ (appendChild row . Just) (valTds ++ [sep] ++ childTds)
           return row
    where toValTd i = do Just td <- createElement w (Just "td")
                         setInnerHTML td (Just $ if v i then "T" else "F")
                         setAttribute td "class" "valtd"
                         return td

          toChildTd (c,m,mg) = do Just td <- createElement w (Just "td")
                                  case c of
                                      Left '⊢' -> case mvalid of
                                                   Just tv -> addDropdown ("turnstileMark" `inOpts` opts) m td tv mg
                                                   Nothing -> setInnerHTML td (Just "")
                                      Left c'  -> setInnerHTML td (Just "")
                                      Right f  -> do let (Form tv) = satisfies v f
                                                     case preview _propIndex f of
                                                         Just i -> addDropdown False m td tv (if "autoAtoms" `inOpts` opts then  (Just $ v i) else mg)
                                                         Nothing -> addDropdown False m td tv mg
                                  return td

          addDropdown turnstileMark m td bool mg = 
                                     do case mg of 
                                            Nothing -> modifyIORef gridRef (M.insert (n,m) False)
                                            Just True -> modifyIORef gridRef (M.insert (n,m) bool)
                                            Just False -> modifyIORef gridRef (M.insert (n,m) (not bool))
                                        case mg of
                                            Just val | "strictGivens" `inOpts` opts || "immutable" `inOpts` opts ->
                                                 do Just span <- createElement w (Just "span")
                                                    if val then setInnerHTML span (Just $ if turnstileMark then "✓" else "T")
                                                           else setInnerHTML span (Just $ if turnstileMark then "✗" else "F")
                                                    appendChild td (Just span)
                                            _ | "immutable" `inOpts` opts -> 
                                                 do Just span <- createElement w (Just "span")
                                                    setInnerHTML span (Just "-")
                                                    appendChild td (Just span)
                                            _ -> do sel <- trueFalseOpts w turnstileMark mg
                                                    onSwitch <- newListener $ switchOnMatch m bool
                                                    addListener sel change onSwitch False
                                                    appendChild td (Just sel)
                                        return ()

          switchOnMatch m tv = do 
                             Just t <- target :: EventM HTMLSelectElement Event (Maybe HTMLSelectElement)
                             s <- getValue t 
                             if s `elem` [Just "T", Just "✓"]
                                 then liftIO $ modifyIORef gridRef (M.insert (n,m) tv)
                                 else liftIO $ modifyIORef gridRef (M.insert (n,m) (not tv))

----------------------------
--  Partial Truth Tables  --
----------------------------

createPartialTruthTable :: Document -> ([PureForm],[PureForm]) -> (Element,Element) -> IORef Bool 
    -> Element -> Map String String -> IO (IO Bool,[Element])
createPartialTruthTable w (gs,fs) (i,o) _ _ opts = 
        do (table, thead, tbody) <- initTable w
           setInnerHTML i (Just . intercalate ", " . map (rewriteWith opts . show) $ fs)
           rRef <- makeRowRef (length orderedChildren)
           head <- toPartialHead
           row <- toPartialRow' rRef valuations givens
           appendChild tbody (Just row)
           appendChild thead (Just head)
           appendChild o (Just table)
           return (check rRef,[row])
    where atomIndicies = nub . sort . concatMap getIndicies $ fs ++ gs
          valuations = (map toValuation) . subsequences $ reverse atomIndicies
          orderedConstraints = concat . intersperse [Left ','] . map toOrderedChildren $ gs
          orderedSolvables = concat . intersperse [Left ','] . map toOrderedChildren $ fs
          orderedChildren = orderedConstraints ++ orderedSolvables
          givens = makeGivens opts Nothing orderedChildren
          toPartialRow' = toPartialRow w opts orderedSolvables orderedConstraints 
          makeRowRef x = newIORef (M.fromList [(z, Nothing) | z <- [1..x]])
          toPartialHead = 
                do Just row <- createElement w (Just "tr")
                   childThs <- mapM (toChildTh w) orderedSolvables >>= rewriteThs opts
                   case orderedConstraints of 
                        [] -> mapM_ (appendChild row . Just) childThs
                        _  -> do Just sep <- createElement w (Just "th")
                                 setAttribute sep "class" "ttthSep"
                                 constraintThs <- mapM (toChildTh w) orderedConstraints >>= rewriteThs opts
                                 mapM_ (appendChild row . Just) constraintThs
                                 appendChild row (Just sep)
                                 mapM_ (appendChild row . Just) childThs
                   return row
          check rRef = do rMap <- readIORef rRef
                          let fittingVals = filter (\v -> any (fitsGiven v) givens) valuations
                          return $ any (validates rMap) fittingVals
          validates rMap v = all (matches rMap v) (zip orderedChildren [1 ..])
          fitsGiven v given = and (zipWith (~=) (map (reform v) orderedChildren) given)
                where reform v (Left c) = Left c
                      reform v (Right f) = Right (unform . satisfies v $ f)
                      (~=) _ Nothing           = True
                      (~=) (Left _) _          = True
                      (~=) (Right t) (Just t') = t == t'
          matches rMap v (Left _,_) = True
          matches rMap v (Right f,m) = 
            case M.lookup m rMap of
                Just (Just tv) -> Form tv == satisfies v f
                _ -> False

toPartialRow w opts orderedSolvables orderedConstraints rRef v givens = 
        do Just row <- createElement w (Just "tr")
           solveTds <- mapM toChildTd (Prelude.drop sepIndex zipped)
           case orderedConstraints of
               [] -> mapM_ (appendChild row . Just) solveTds
               _ -> do Just sep <- createElement w (Just "td")
                       setAttribute sep "class" "tttdSep"
                       constraintTds <- mapM toConstTd (take sepIndex zipped)
                       mapM_ (appendChild row . Just) constraintTds
                       appendChild row (Just sep)
                       mapM_ (appendChild row . Just) solveTds
           return row

    where sepIndex = length orderedConstraints
          zipped = zip3 (orderedConstraints ++ orderedSolvables) [1 ..] givenRow
          givenRow = last givens
          --XXX The givens are passed around in reverse order - this is
          --actually the first row
          toChildTd (c,m,mg) = do Just td <- createElement w (Just "td")
                                  case c of
                                      Left _ -> setInnerHTML td (Just "")
                                      Right _ -> addDropdown m td mg
                                  return td

          toConstTd (c,m,mg) = do Just td <- createElement w (Just "td")
                                  case c of
                                      Left _ -> setInnerHTML td (Just "")
                                      Right _ -> case mg of
                                         --TODO: DRY
                                         Just val -> do Just span <- createElement w (Just "span")
                                                        setInnerHTML span (Just $ if val then "T" else "F")
                                                        modifyIORef rRef (M.insert m mg)
                                                        appendChild td (Just span)
                                                        return ()
                                         Nothing ->  do sel <- trueFalseOpts w False mg
                                                        modifyIORef rRef (M.insert m mg)
                                                        onSwitch <- newListener $ switch rRef m
                                                        addListener sel change onSwitch False
                                                        appendChild td (Just sel)
                                                        return ()
                                  return td

          addDropdown m td mg = do case mg of
                                       Just val | "strictGivens" `inOpts` opts || "immutable" `inOpts` opts -> 
                                            do Just span <- createElement w (Just "span")
                                               setInnerHTML span (Just $ if val then "T" else "F")
                                               modifyIORef rRef (M.insert m mg)
                                               appendChild td (Just span)
                                       Just val | "hiddenGivens" `inOpts` opts -> 
                                            do sel <- trueFalseOpts w False Nothing
                                               onSwitch <- newListener $ switch rRef m
                                               addListener sel change onSwitch False
                                               appendChild td (Just sel)
                                       _ | "immutable" `inOpts` opts -> 
                                            do Just span <- createElement w (Just "span")
                                               setInnerHTML span (Just "-")
                                               appendChild td (Just span)
                                       _ -> do sel <- trueFalseOpts w False mg
                                               modifyIORef rRef (M.insert m mg)
                                               onSwitch <- newListener $ switch rRef m
                                               addListener sel change onSwitch False
                                               appendChild td (Just sel)
                                   return ()

          switch rRef m = do 
                 Just t <- target :: EventM HTMLSelectElement Event (Maybe HTMLSelectElement)
                 tv <- stringToTruthValue <$> getValue t 
                 liftIO $ modifyIORef rRef (M.insert m tv)

------------------------
--  HTML Boilerplate  --
------------------------

trueFalseOpts :: Document -> Bool -> Maybe Bool -> IO Element
trueFalseOpts w turnstileMark mg = 
        do Just sel <- createElement w (Just "select")
           Just bl  <- createElement w (Just "option")
           Just tr  <- createElement w (Just "option")
           Just fs  <- createElement w (Just "option")
           setInnerHTML bl (Just "-")
           setInnerHTML tr (Just $ if turnstileMark then "✓" else "T")
           setInnerHTML fs (Just $ if turnstileMark then "✗" else "F")
           case mg of
               Nothing -> return ()
               Just True -> setAttribute tr "selected" "selected"
               Just False -> setAttribute fs "selected" "selected"
           appendChild sel (Just bl)
           appendChild sel (Just tr)
           appendChild sel (Just fs)
           return sel

toHead w opts atomIndicies orderedChildren = 
        do Just row <- createElement w (Just "tr")
           Just sep <- createElement w (Just "th")
           setAttribute sep "class" "ttthSep"
           atomThs <- mapM toAtomTh atomIndicies
           childThs <- mapM (toChildTh w) orderedChildren >>= rewriteThs opts
           mapM_ (appendChild row . Just) atomThs
           appendChild row (Just sep)
           mapM_ (appendChild row . Just) childThs
           return row
    where toAtomTh i = do Just th <- createElement w (Just "th")
                          setInnerHTML th (Just $ show (pn i :: PureForm))
                          return th

toChildTh :: (Schematizable (f (FixLang f)), CopulaSchema (FixLang f)) => Document -> Either Char (FixLang f a) -> IO Element
toChildTh w c = 
        do Just th <- createElement w (Just "th")
           case c of
               Left '⊢' -> do setInnerHTML th (Just ['⊢'])
                              setAttribute th "class" "ttTurstile"
               Left c'  -> setInnerHTML th (Just [c'])
               Right f  -> setInnerHTML th (Just $ mcOf f)
           return th

-----------
--  BPT  --
-----------
--we use a new data structure to convert formulas to ordered lists of
--subformulas and appropriate parentheses

--Binary propositional parsing tree. This could be written more compactly,
--but this seems conceptually clearer
data BPT = Leaf PureForm | MonNode PureForm BPT | BiNode PureForm BPT BPT

toBPT :: PureForm -> BPT
toBPT f = case children f of
              [a] -> MonNode f (toBPT a)
              [a,b] -> BiNode f (toBPT a) (toBPT b)
              _ -> Leaf f


traverseBPT :: BPT -> [Either Char PureForm]
traverseBPT (Leaf f) = [Right f]
traverseBPT (MonNode f a) = [Right f] ++ traverseBPT a
traverseBPT (BiNode f a b) = [Left '('] ++ traverseBPT a ++ [Right f] ++ traverseBPT b ++ [Left ')']

toOrderedChildren = traverseBPT . toBPT

-------------------------
--  Utility Functions  --
-------------------------

--this is a sorting that gets the correct ordering of indicies (reversed on
--negative, negative less than positive, postive as usual)
sort :: [Int] -> [Int]
sort (x:xs) = smaller ++ [x] ++ bigger
    where smaller = sort (Prelude.filter small xs )
          bigger = sort (Prelude.filter (not . small) xs)
          small y | x < 0 && y > 0 = False
                  | x < 0 && y < 0 = x < y
                  | otherwise = y < x
sort [] = []

unpackRow :: Element -> IO [Maybe Bool]
unpackRow row = getListOfElementsByTag row "select" >>= mapM toValue
    where toValue (Just e) = do stringToTruthValue <$> getValue (castToHTMLSelectElement e)
          toValue Nothing = return Nothing

packText :: String -> [Maybe Bool]
packText s = if valid then map charToTruthValue . filter (/= ' ') $ s else []
    where valid = all (`elem` ['T','F','-',' ']) s

expandRow :: [Either Char b] -> [Maybe Bool] ->  [Maybe Bool]
expandRow (Right y:ys)  (x:xs)  = x : expandRow ys xs 
expandRow (Left '⊢':ys) (x:xs)  = x : expandRow ys xs 
expandRow (Left y:ys) xs  = Nothing : expandRow ys xs
expandRow [] (x:xs)       = Nothing : expandRow [] xs
expandRow _ _ = []

initTable :: Document -> IO (Element, Element, Element)
initTable w = do (Just table) <- createElement w (Just "table")
                 (Just thead) <- createElement w (Just "thead")
                 (Just tbody) <- createElement w (Just "tbody")
                 appendChild table (Just thead)
                 appendChild table (Just tbody)
                 return (table, thead, tbody)

toValuation :: [Int] -> (Int -> Bool)
toValuation = flip elem

makeGridRef :: Int -> Int -> IO (IORef (Map (Int,Int) Bool))
makeGridRef x y = newIORef (M.fromList [((z,w), True) | z <- [1..x], w <-[1.. y]])

rewriteThs :: Map String String -> [Element] -> IO [Element]
rewriteThs opts ths = do s <- map deMaybe <$> mapM getInnerHTML ths
                         let s' = rewriteWith opts . concat $ s
                         mapM (\(c, th) -> setInnerHTML th (Just [c])) $ zip s' ths
                         return ths
    where deMaybe (Just c) = c
          deMaybe Nothing = " "

charToTruthValue :: Char -> Maybe Bool
charToTruthValue 'T' = Just True
charToTruthValue 'F' = Just False
charToTruthValue _   = Nothing 

stringToTruthValue :: Maybe String -> Maybe Bool
stringToTruthValue (Just [c]) = charToTruthValue c
stringToTruthValue _   = Nothing 

rewriteWith :: Map String String -> String -> String
rewriteWith opts = case M.lookup "system" opts >>= ofPropSys ndNotation of
                        Just f -> f
                        Nothing -> id

mcOf :: (Schematizable (f (FixLang f)), CopulaSchema (FixLang f)) => FixLang f a -> String
mcOf (h :!$: t) = mcOf h
mcOf h = show h

inOpts :: String -> Map String String -> Bool
inOpts s opts = s `elem` optList
    where optList = case M.lookup "options" opts of Just s -> words s; Nothing -> []
          
unform :: Form Bool -> Bool
unform (Form b) = b

makeGivens :: Map String String -> Maybe Int -> [Either Char (FixLang f a)] -> [[Maybe Bool]]
makeGivens opts mrows orderedChildren = case M.lookup "content" opts of 
       Nothing -> repeat $ repeat Nothing
       Just t -> case (reverse . map packText . filter (not . blank) . lines $ t, mrows) of
                     (s, Just rows) | length s == rows -> checkRowstrings rows s
                                    | otherwise -> take rows $ repeat $ repeat Nothing
                     (s, Nothing) | length s > 0 -> checkRowstrings 1 s
                                  | otherwise -> [repeat Nothing]
    where checkRowstrings rows rowstrings = 
            case map (expandRow orderedChildren) rowstrings of
               s' | all (\x -> length x == length orderedChildren) s' -> s'
                  | otherwise -> take rows $ repeat $ repeat Nothing
          blank = all (`elem` [' ','\t'])

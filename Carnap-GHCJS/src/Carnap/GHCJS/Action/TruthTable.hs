{-# LANGUAGE RankNTypes, FlexibleContexts #-}
module Carnap.GHCJS.Action.TruthTable (truthTableAction) where

import Lib
import Carnap.GHCJS.SharedTypes
import Carnap.Core.Data.Types
import Carnap.Core.Data.Classes (Schematizable, Modelable(..))
import Carnap.Calculi.NaturalDeduction.Syntax (NaturalDeductionCalc(..))
import Carnap.Languages.PurePropositional.Logic (montagueSCCalc)
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Util (getIndicies)
import Carnap.Languages.PurePropositional.Syntax (PureForm)
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.PurePropositional.Logic (PropSequentCalc)
import Carnap.Languages.Util.LanguageClasses
import GHCJS.DOM.Types
import GHCJS.DOM.Element
--import GHCJS.DOM.HTMLOptionElement (getValue)
import GHCJS.DOM.HTMLSelectElement (castToHTMLSelectElement, getValue) 
import GHCJS.DOM.Window (alert, prompt)
import GHCJS.DOM.Document (createElement, getBody, getDefaultView)
import GHCJS.DOM.Node (appendChild, getParentNode, insertBefore)
import GHCJS.DOM.EventM (newListener, addListener, EventM, target)
import Data.IORef (newIORef, IORef, readIORef,writeIORef, modifyIORef)
import Data.Map as M (Map, lookup, foldr, insert, fromList, toList)
import Data.Text (pack)
import Data.List (subsequences, nub, zip4,intersperse)
import Control.Monad.IO.Class (liftIO)
import Control.Lens (toListOf, preview)
import Control.Lens.Plated (children)
import Text.Parsec (parse, ParseError, eof)

truthTableAction :: IO ()
truthTableAction = initElements getTruthTables activateTruthTables

getTruthTables :: Document -> HTMLElement -> IO [Maybe (Element, Element, Map String String)]
getTruthTables d = genInOutElts d "div" "div" "truthtable"

activateTruthTables :: Document -> Maybe (Element, Element, Map String String) -> IO ()
activateTruthTables w (Just (i,o,opts)) = 
        case M.lookup "tabletype" opts of
            (Just "simple") -> checkerWith (purePropFormulaParser standardLetters <* eof) createSimpleTruthTable
            (Just "validity") -> checkerWith (ndParseSeq montagueSCCalc) createValidityTruthTable
            _  -> return ()
    where optlist = case M.lookup "options" opts of Just s -> words s; Nothing -> []
          checkerWith parser ttfunc = 
            case M.lookup "goal" opts of
                Just g ->
                  case parse parser "" g of
                      Right f -> do
                          ref <- newIORef False
                          bw <- buttonWrapper w
                          (check,rows) <- ttfunc w f (i,o) ref bw opts
                          case M.lookup "submission" opts of
                              Just s | take 7 s == "saveAs:" -> do
                                  let l = Prelude.drop 7 s
                                  bt1 <- doneButton w "Submit"
                                  appendChild bw (Just bt1)
                                  submit <- newListener $ submitTruthTable opts ref check rows (show f) l
                                  addListener bt1 click submit False                
                              _ -> return ()
                          if "nocheck" `elem` optlist then return () 
                          else do
                              bt2 <- questionButton w "Check"
                              appendChild bw (Just bt2)
                              checkIt <- newListener $ checkTable ref check
                              addListener bt2 click checkIt False                
                          (Just par) <- getParentNode o
                          appendChild par (Just bw)
                          setInnerHTML i (Just $ show f)
                      (Left e) -> setInnerHTML o (Just $ show e) 
                _ -> print "truth table was missing an option"
          checkTable ref check = do correct <- liftIO $ check
                                    if correct 
                                        then do message "Success!"
                                                liftIO $ writeIORef ref True
                                                setAttribute i "class" "input completeTT"
                                        else do message "Something's not quite right"
                                                setAttribute i "class" "input incompleteTT"

submitTruthTable:: M.Map String String -> IORef Bool ->  IO Bool -> [Element] -> String -> String -> EventM HTMLInputElement e ()
submitTruthTable opts ref check rows s l = do isDone <- liftIO $ readIORef ref
                                              if isDone 
                                                 then trySubmit TruthTable opts l (ProblemContent (pack s)) True
                                                 else if "exam" `elem` optlist
                                                          then do correct <- liftIO check
                                                                  if correct
                                                                      then trySubmit TruthTable opts l (ProblemContent (pack s)) True
                                                                      else do tabulated <- liftIO $ mapM unpackRow rows
                                                                              trySubmit TruthTable opts l (TruthTableDataOpts (pack s) (reverse tabulated) (M.toList opts)) False
                                                          else message "not yet finished (do you still need to check your answer?)"
    where optlist = case M.lookup "options" opts of Just s -> words s; Nothing -> []

createValidityTruthTable :: Document -> PropSequentCalc (Sequent (Form Bool)) 
    -> (Element,Element) -> IORef Bool -> Element -> Map String String
    -> IO (IO Bool, [Element])
createValidityTruthTable w (antced :|-: (SS succed)) (i,o) ref bw opts =
        do (table, thead, tbody) <- initTable w
           gRef <- makeGridRef (length orderedChildren) (length valuations)
           let validities = Prelude.map (Just . implies) valuations
               givens = case M.lookup "content" opts of 
                           Nothing -> repeat $ repeat Nothing
                           Just t -> case (reverse . map packText $ lines t) of
                                         s | length s == length valuations -> 
                                           case map (expandRow orderedChildren) s of
                                               s' | all (\x -> length x == length orderedChildren) s' -> s'
                                                  | otherwise -> repeat $ repeat Nothing
                                           | otherwise -> repeat $ repeat Nothing
           head <- toHead w atomIndicies orderedChildren
           rows <- mapM (toRow' gRef) (zip4 valuations [1..] validities givens)
           mapM_ (appendChild tbody . Just) (reverse rows)
           (Just w') <- getDefaultView w                    
           if "nocounterexample" `elem` optlist 
               then return ()
               else do bt <- exclaimButton w "Counterexample"
                       counterexample <- newListener $ tryCounterexample w'
                       addListener bt click counterexample False
                       appendChild bw (Just bt)
                       return ()
           appendChild thead (Just head)
           appendChild o (Just table)
           mpar@(Just par) <- getParentNode o
           let check = M.foldr (&&) True <$> readIORef gRef 
           return (check ,rows)
    where forms :: [PureForm]
          forms = (Prelude.map fromSequent $ toListOf concretes antced) ++ (Prelude.map fromSequent $ toListOf concretes succed)
          implies v = not (and (Prelude.map (unform . satisfies v) (init forms))) || (unform . satisfies v $ last forms)
          optlist = case M.lookup "options" opts of Just s -> words s; Nothing -> []
          unform (Form b) = b
          atomIndicies = nub . sort . concat $ (Prelude.map getIndicies forms) 
          toValuation l = \x -> x `elem` l
          valuations = (Prelude.map toValuation) . subsequences $ reverse atomIndicies
          orderedChildren = concat $ intersperse [Left ','] (Prelude.map (traverseBPT . toBPT. fromSequent) (toListOf concretes antced))
                            ++ [[Left '⊢']] ++ intersperse [Left ','] (Prelude.map (traverseBPT . toBPT. fromSequent) (toListOf concretes succed))
          toRow' = toRow w opts atomIndicies orderedChildren o 
          makeGridRef x y = newIORef (M.fromList [((z,w), True) | z <- [1..x], w <-[1.. y]])
          tryCounterexample w' = do mrow <- liftIO $ prompt w' "enter the truth values for your counterexample row" (Just "")
                                    case mrow of 
                                        Nothing -> return ()
                                        Just s -> 
                                            case checkLength =<< (clean $ Prelude.map toTV s) of
                                              Nothing -> alert w' "not a readable row"
                                              Just l -> do let v = listToVal l
                                                           let s = not $ implies v
                                                           if s then do alert w' "Success!"
                                                                        liftIO $ writeIORef ref True
                                                                        setAttribute i "class" "completeTT"
                                                                else do alert w' "Something's not quite right"
                                                                        setAttribute i "class" "incompleteTT"
            where toTV 'T' = Just True
                  toTV 'F' = Just False
                  toTV _   = Nothing 
                  clean (Nothing:xs) = Nothing
                  clean (Just x:xs) = (:) <$> (Just x) <*> (clean xs)
                  clean [] = Just []
                  listToVal l = toValuation (mask l atomIndicies)
                  mask (x:xs) (y:ys) = if x then y:(mask xs ys) else mask xs ys
                  mask [] _ = []
                  checkLength l = if length l == length atomIndicies then Just l else Nothing

createSimpleTruthTable :: Document -> PureForm -> (Element,Element) -> IORef Bool 
    -> Element -> Map String String 
    -> IO (IO Bool,[Element])
createSimpleTruthTable w f (_,o) _ _ opts = 
        do (table, thead, tbody) <- initTable w
           gRef <- makeGridRef (length orderedChildren) (length valuations)
           head <- toHead w atomIndicies orderedChildren
           let givens = case M.lookup "content" opts of 
                           Nothing -> repeat $ repeat Nothing
                           Just t -> case (reverse . map packText $ lines t) of
                                         s | length s == length valuations -> 
                                           case map (expandRow orderedChildren) s of
                                               s' | all (\x -> length x == length orderedChildren) s' -> s'
                                                  | otherwise -> repeat $ repeat Nothing
                                           | otherwise -> repeat $ repeat Nothing
           rows <- mapM (toRow' gRef) (zip4 valuations [1..] (repeat Nothing) givens)
           mapM_ (appendChild tbody . Just) (reverse rows)
           setInnerHTML o (Just "")
           appendChild thead (Just head)
           appendChild o (Just table)
           let check = M.foldr (&&) True <$> readIORef gRef 
           return (check,rows)
    where atomIndicies = nub . sort . getIndicies $ f
          valuations = (Prelude.map toValuation) . subsequences $ reverse atomIndicies
            where toValuation l = \x -> x `elem` l
          orderedChildren =  traverseBPT . toBPT $ f
          toRow' = toRow w opts atomIndicies orderedChildren o
          makeGridRef x y = newIORef (M.fromList [((z,w), True) | z <- [1..x], w <-[1.. y]])

-- createPartialTruthTable :: Document -> PureForm -> (Element,Element) -> IORef Bool 
--     -> Element -> Map String String 
--     -> IO (IORef (Map (Int, Int) Bool),[Element])
-- createPartialTruthTable w f (_,o) _ _ opts = 
--         do (table, thead, tbody) <- initTable w
--            gRef <- makeRowRef (length orderedChildren)
--            head <- toHead w atomIndicies orderedChildren
--            let givens = case M.lookup "content" opts of 
--                            Nothing -> repeat $ repeat Nothing
--                            Just t -> let t' = expandRow orderedChildren t in
--                                            if length t' == length orderedChildren 
--                                                then t'
--                                                else repeat Nothing
--            rows <- toRow' gRef (zip4 valuations [1..] (repeat Nothing) givens)
--            appendChild tbody (Just rows)
--            setInnerHTML o (Just "")
--            appendChild thead (Just head)
--            appendChild o (Just table)
--            return (gRef,rows)
--     where atomIndicies = nub . sort . getIndicies $ f
--           valuations = (Prelude.map toValuation) . subsequences $ reverse atomIndicies
--             where toValuation l = \x -> x `elem` l
--           orderedChildren =  traverseBPT . toBPT $ f
--           toRow' = toRow w opts atomIndicies orderedChildren o
--           makeRowRef x = newIORef (M.fromList [(z, True) | z <- [1..x]])

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

toRow w opts atomIndicies orderedChildren o gRef (v,n,mvalid,given) = 
        do (Just row) <- createElement w (Just "tr")
           (Just sep) <- createElement w (Just "td")
           setAttribute sep "class" "tttdSep"
           valTds <- mapM toValTd atomIndicies
           childTds <- mapM toChildTd (zip3 orderedChildren [1..] given)
           mapM_ (appendChild row . Just) valTds
           appendChild row (Just sep)
           mapM_ (appendChild row . Just) childTds
           return row
    where toValTd i = do (Just td) <- createElement w (Just "td")
                         setInnerHTML td (Just $ if v i then "T" else "F")
                         setAttribute td "class" "valtd"
                         return td

          toChildTd (c,m,mg) = do (Just td) <- createElement w (Just "td")
                                  case c of
                                      Left '⊢' -> case mvalid of
                                                   (Just tv) -> addDropdown m td tv mg
                                                   Nothing -> setInnerHTML td (Just "")
                                      Left c'  -> setInnerHTML td (Just "")
                                      Right f  -> do let (Form tv) = satisfies v f
                                                     case preview _propIndex f of
                                                         Just i -> addDropdown m td tv (if "autoAtoms" `elem` optlist then  (Just $ v i) else mg)
                                                         Nothing -> addDropdown m td tv mg

                                  return td

          addDropdown m td bool mg = do sel <- trueFalseOpts mg
                                        appendChild td (Just sel)
                                        case mg of 
                                            Nothing -> modifyIORef gRef (M.insert (n,m) False)
                                            Just True -> modifyIORef gRef (M.insert (n,m) bool)
                                            Just False -> modifyIORef gRef (M.insert (n,m) (not bool))
                                        onSwitch <- newListener $ switchOnMatch gRef (n,m) bool
                                        addListener sel change onSwitch False
                                        return ()

          trueFalseOpts mg = do (Just sel) <- createElement w (Just "select")
                                (Just bl)  <- createElement w (Just "option")
                                (Just tr)  <- createElement w (Just "option")
                                (Just fs)  <- createElement w (Just "option")
                                setInnerHTML bl (Just "-")
                                setInnerHTML tr (Just "T")
                                setInnerHTML fs (Just "F")
                                case mg of
                                    Nothing -> return ()
                                    Just True -> setAttribute tr "selected" "selected"
                                    Just False -> setAttribute fs "selected" "selected"
                                appendChild sel (Just bl)
                                appendChild sel (Just tr)
                                appendChild sel (Just fs)
                                return sel

          switchOnMatch gRef (n,m) tv = do 
                             (Just t) <- target :: EventM HTMLSelectElement Event (Maybe HTMLSelectElement)
                             s <- getValue t 
                             if s == Just "T" 
                                 then liftIO $ modifyIORef gRef (M.insert (n,m) tv)
                                 else liftIO $ modifyIORef gRef (M.insert (n,m) (not tv))
          optlist = case M.lookup "options" opts of Just s -> words s; Nothing -> []

toHead w atomIndicies orderedChildren = 
        do (Just row) <- createElement w (Just "tr")
           (Just sep) <- createElement w (Just "th")
           setAttribute sep "class" "ttthSep"
           atomThs <- mapM toAtomTh atomIndicies
           childThs <- mapM toChildTh orderedChildren
           mapM_ (appendChild row . Just) atomThs
           appendChild row (Just sep)
           mapM_ (appendChild row . Just) childThs
           return row
    where toAtomTh i = do (Just td) <- createElement w (Just "th")
                          setInnerHTML td (Just $ show (pn i :: PureForm))
                          return td
          toChildTh c = do (Just td) <- createElement w (Just "th")
                           case c of
                               Left '⊢' -> do setInnerHTML td (Just ['⊢'])
                                              setAttribute td "class" "ttTurstile"
                               Left c'  -> setInnerHTML td (Just [c'])
                               Right f  -> setInnerHTML td (Just $ mcOf f)
                           return td
          mcOf :: (Schematizable (f (FixLang f)), CopulaSchema (FixLang f)) => FixLang f a -> String
          mcOf (h :!$: t) = mcOf h
          mcOf h = show h

--Binary propositional parsing tree. This could be written more compactly,
--but this seems conceptually clearer
data BPT = Leaf PureForm | MonNode PureForm BPT | BiNode PureForm BPT BPT

toBPT :: PureForm -> BPT
toBPT f = case children f of
              [a] -> MonNode f (toBPT a)
              [a,b] -> BiNode f (toBPT a) (toBPT b)
              _ -> Leaf f

unpackRow :: Element -> IO [Maybe Bool]
unpackRow row = getListOfElementsByTag row "select" >>= mapM toValue
    where toValue (Just e) = do s <- getValue (castToHTMLSelectElement e)
                                return $ case s of 
                                  Just "T" -> Just True
                                  Just "F" -> Just False
                                  _ -> Nothing
          toValue Nothing = return Nothing

packText :: String -> [Maybe Bool]
packText s = if valid then map toValue . filter (/= ' ') $ s else []
    where toValue 'T' = Just True
          toValue 'F' = Just False
          toValue _ = Nothing

          valid = all (`elem` ['T','F','-',' ']) s

expandRow :: [Either Char b] -> [Maybe Bool] ->  [Maybe Bool]
expandRow (Right y:ys)  (x:xs)  = x : expandRow ys xs 
expandRow (Left '⊢':ys) (x:xs)  = x : expandRow ys xs 
expandRow (Left y:ys) xs  = Nothing : expandRow ys xs
expandRow [] (x:xs)       = Nothing : expandRow [] xs
expandRow _ _ = []

traverseBPT :: BPT -> [Either Char PureForm]
traverseBPT (Leaf f) = [Right f]
traverseBPT (MonNode f a) = [Right f] ++ traverseBPT a
traverseBPT (BiNode f a b) = [Left '('] ++ traverseBPT a ++ [Right f] ++ traverseBPT b ++ [Left ')']

initTable :: Document -> IO (Element, Element, Element)
initTable w = do (Just table) <- createElement w (Just "table")
                 (Just thead) <- createElement w (Just "thead")
                 (Just tbody) <- createElement w (Just "tbody")
                 appendChild table (Just thead)
                 appendChild table (Just tbody)
                 return (table, thead, tbody)

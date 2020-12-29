{-# LANGUAGE RankNTypes, QuasiQuotes, FlexibleContexts, DeriveDataTypeable, CPP, JavaScriptFFI #-}
module Lib ( genericSendJSON, sendJSON, onEnter, onKey, doOnce, dispatchCustom, allDone
           , clearInput, getListOfElementsByClass, getListOfElementsByTag, getCarnapDataMap, tryParse
           , treeToElement, genericTreeToUl, treeToUl, genericListToUl
           , listToUl, formToTree, leaves, adjustFirstMatching, decodeHtml
           , decodeJSON,toJSONString, cleanString, syncScroll, reloadPage, initElements
           , errorPopup, genInOutElts
           , getInOutElts,generateExerciseElts, withLabel
           , formAndLabel,seqAndLabel, folSeqAndLabel, folFormAndLabel
           , message, IOGoal(..), updateWithValue, submissionSource
           , assignmentKey, initialize, mutate, initializeCallback, initCallbackObj
           , toCleanVal, popUpWith, spinnerSVG, doneButton, questionButton
           , exclaimButton, expandButton, createSubmitButton, createButtonWrapper
           , maybeNodeListToList, trySubmit, inOpts, rewriteWith, setStatus, setSuccess, setFailure
           , ButtonStatus(..) , keyString) where

import Data.Aeson
import Data.Maybe (catMaybes)
import qualified Data.ByteString.Lazy as BSL
import Data.Text (pack)
import Data.Text.Encoding
import Data.Tree as T
import Data.IORef (IORef, readIORef)
import qualified Data.Map as M
import Text.Read (readMaybe)
import Text.Parsec
import Text.StringLike
import Text.HTML.TagSoup as TS
import Text.Hamlet
import Text.Blaze.Html.Renderer.String
import Control.Lens
import Control.Lens.Plated (children)
import Control.Monad.Fix
import Control.Monad.State
import Control.Monad.Trans.Maybe (runMaybeT, MaybeT(..))
--The following three imports come from ghcjs-base, and break ghc-mod
#ifdef __GHCJS__
import GHCJS.Types
import GHCJS.Foreign
import GHCJS.Foreign.Callback
import GHCJS.Marshal
#endif
--the import below required to make ghc-mod work properly. GHCJS compiles
--using the generated javascript FFI versions of 2.4.0, but those are
--slightly different from the webkit versions of 2.4.0. In particular,
--Element doesn't export IsElement, although Types does in the webkit
--version---but it's the other way around in the FFI version. This appears
--to be cleaner in 3.0, but there's no documentation for that at all, yet.
import GHCJS.DOM
import GHCJS.DOM.Types
import GHCJS.DOM.Element
import GHCJS.DOM.HTMLInputElement
import qualified GHCJS.DOM.HTMLTextAreaElement as TA (setValue,getValue)
import GHCJS.DOM.Document (createElement, getBody, createEvent)
import GHCJS.DOM.Node
import qualified GHCJS.DOM.HTMLCollection as HC
import GHCJS.DOM.NodeList
import qualified GHCJS.DOM.NamedNodeMap as NM
import GHCJS.DOM.Event as EV
import GHCJS.DOM.KeyboardEvent
import GHCJS.DOM.EventM
import GHCJS.DOM.EventTarget
import GHCJS.DOM.EventTargetClosures (EventName(..))
import Carnap.GHCJS.SharedTypes
import Carnap.GHCJS.SharedFunctions
import Carnap.Calculi.NaturalDeduction.Syntax (NaturalDeductionCalc(..))
import Carnap.Languages.PurePropositional.Syntax (PureForm)
import Carnap.Languages.PurePropositional.Logic
import Carnap.Languages.PureFirstOrder.Parser (folFormulaParser)
import Carnap.Languages.PureFirstOrder.Logic
import Carnap.Languages.PurePropositional.Parser (purePropFormulaParser, standardLetters)

--------------------------------------------------------
--1. Utility Functions
--------------------------------------------------------

---------------------------
--  1.0 Simple Patterns  --
---------------------------


--------------------------------------------------------
--1.1 Events
--------------------------------------------------------

onKey :: [String] -> EventM e KeyboardEvent () ->  EventM e KeyboardEvent ()
onKey keylist action = do kbe      <- event
                          id       <- getKeyIdentifier kbe 
                          -- XXX: keyIdentifier is deprecated and doesn't work in
                          -- firefox; hence the use of `keyString`. But `key`
                          -- doesn't work in some older browsers, so we keep
                          -- this line around.
                          id'      <- liftIO $ keyString kbe
                          
                          if id `elem` keylist || id' `elem` keylist 
                              then EV.preventDefault kbe >> action 
                              else return ()

onEnter :: EventM e KeyboardEvent () ->  EventM e KeyboardEvent ()
onEnter = onKey ["Enter"]

doOnce :: (IsEventTarget t, IsEvent e) => t -> EventName t e -> Bool -> EventM t e r ->  IO ()
doOnce target event bubble handler = do listener <- mfix $ \rec -> newListener  $ do
                                                        handler 
                                                        liftIO $ removeListener target event rec bubble 
                                        addListener target event listener bubble

dispatchCustom :: IsEventTarget t => Document -> t -> String -> IO ()
dispatchCustom w e s = do Just custom <- createEvent w "Event"
                          initEvent custom s True True
                          dispatchEvent e (Just custom)
                          return ()

allDone :: IO ()
allDone = runWebGUI $ \w -> 
    do Just dom <- webViewGetDomDocument w
       dispatchCustom dom dom "carnap-loaded"

--------------------------------------------------------
--1.1.2 Common responsive behavior
--------------------------------------------------------

syncScroll e1 e2 = do cup1 <- catchup e1 e2
                      cup2 <- catchup e2 e1
                      addListener e1 scroll cup1 False
                      addListener e2 scroll cup2 False
    where catchup e1 e2 = newListener $ liftIO $ do st <- getScrollTop e1
                                                    setScrollTop e2 st

--------------------------------------------------------
--1.2 DOM Manipulation
--------------------------------------------------------

--------------------------------------------------------
--1.2.1 DOM Data
--------------------------------------------------------
-- data structures for DOM elements

data IOGoal = IOGoal { inputArea :: Element
                     , outputArea :: Element
                     , goalArea :: Element
                     , content :: String
                     , exerciseOptions :: M.Map String String
                     }

clearInput :: (MonadIO m) => HTMLInputElement -> m ()
clearInput i = setValue i (Just "")

maybeNodeListToList mnl = case mnl of 
                            Nothing -> return []
                            Just nl -> do l <- getLength nl
                                          if l > 0 then 
                                              mapM ((fmap . fmap) castToElement . item nl) [0 .. l-1]
                                          else return []

maybeHtmlCollectionToList mhc = case mhc of 
                            Nothing -> return []
                            Just hc -> do l <- HC.getLength hc
                                          if l > 0 then 
                                              mapM ((fmap . fmap) castToElement . HC.item hc) [0 .. l-1]
                                          else return []

-- XXX: one might also want to include a "mutable lens" or "mutable traversal"
--kind of thing: http://stackoverflow.com/questions/18794745/can-i-make-a-lens-with-a-monad-constraint
getListOfElementsByClass :: IsElement self => self -> String -> IO [Maybe Element]
getListOfElementsByClass elt c = getElementsByClassName elt c >>= maybeNodeListToList

getListOfElementsByTag :: IsElement self => self -> String -> IO [Maybe Element]
getListOfElementsByTag elt c = getElementsByTagName elt c >>= maybeNodeListToList

getListOfElementsByCarnapType :: IsElement self => self -> String -> IO [Maybe Element]
getListOfElementsByCarnapType elt s = querySelectorAll elt ("[data-carnap-type=" ++ s ++ "]") >>= maybeNodeListToList

tryParse p s = unPack $ parse p "" s 
    where unPack (Right s) = show s
          unPack (Left e)  = show e

treeToElement :: (a -> IO Element) -> (Element -> [Element] -> IO ()) -> Tree a -> IO Element
treeToElement f g (T.Node n []) = f n
treeToElement f g (T.Node n ts) = do r <- f n
                                     elts <- mapM (treeToElement f g) ts
                                     g r elts
                                     return r

genericTreeToUl :: (a -> String) -> Document -> Tree (a, String) -> IO Element
genericTreeToUl sf w t = treeToElement itemize listify t
    where itemize (x,c) = do s@(Just s') <- createElement w (Just "li")
                             setInnerHTML s' (Just $ sf x)
                             setAttribute s' "class" c 
                             return s'
          listify x xs = do o@(Just o') <- createElement w (Just "ul")
                            mapM_ (appendChild o' . Just) xs
                            appendChild x o
                            return ()

treeToUl :: Show a => Document -> Tree (a, String) -> IO Element
treeToUl = genericTreeToUl show

genericListToUl :: (Element -> a -> IO ()) -> Document -> [a] -> IO Element
genericListToUl f doc l = 
        do elts <- mapM wrapIt l
           (Just ul) <- createElement doc (Just "ul")
           mapM_ (appendChild ul) elts
           return ul
    where wrapIt e = do (Just li) <- createElement doc (Just "li")
                        f li e 
                        return (Just li)

listToUl :: Show a => Document -> [a] -> IO Element
listToUl = genericListToUl (\e a -> setInnerHTML e (Just $ show a))

{-
This function supports a pattern where we gather a list of elements that
have a designated input (usually a text area or something) and output
children, and then attach events to them according to the classes of their
parents. 
-}
getInOutElts :: IsElement self => String -> self -> IO [Maybe (Element, Element, [String])]
getInOutElts cls b = do els <- getListOfElementsByClass b cls
                        mapM extract els
        where extract Nothing = return Nothing
              extract (Just el) = 
                do cn <- getClassName el
                   runMaybeT $ do
                        i <- MaybeT $ getFirstElementChild el
                        o <- MaybeT $ getNextElementSibling i
                        return (i ,o ,words cn)

genInOutElts :: IsElement self => Document -> String -> String -> String -> self -> IO [Maybe (Element, Element, M.Map String String)]
genInOutElts w input output ty target = 
        do els <- getListOfElementsByCarnapType target ty
           mapM initialize els
    where initialize Nothing = return Nothing
          initialize (Just el) = do
              Just content <- getTextContent el :: IO (Maybe String)
              [Just o, Just i] <- mapM (createElement w . Just) [output,input]
              setAttribute i "class" "input"
              setAttribute o "class" "output"
              setInnerHTML el (Just "")
              opts <- getCarnapDataMap el
              mapM_ (appendChild el . Just) [i,o]
              return $ Just (i, o, M.insert "content" content opts )

generateExerciseElts :: IsElement self => Document -> String -> self -> IO [Maybe IOGoal]
generateExerciseElts w ty target = do els <- getListOfElementsByCarnapType target ty 
                                      mapM initialize els
        where initialize Nothing = return Nothing
              initialize (Just el) = do
                  Just content <- getTextContent el
                  setInnerHTML el (Just "")
                  [Just g, Just o, Just i] <- mapM (createElement w . Just) ["div","div","textarea"]
                  setAttribute g "class" "goal"
                  setAttribute i "class" "input"
                  setAttribute o "class" "output"
                  opts <- getCarnapDataMap el
                  mapM_ (appendChild el . Just) [g,i,o]
                  return $ Just (IOGoal i o g content opts)

updateWithValue :: IsEvent ev => (String ->  IO ()) -> EventM HTMLTextAreaElement ev ()
updateWithValue f = 
        do (Just t) <- target :: IsEvent ev' => EventM HTMLTextAreaElement ev' (Maybe HTMLTextAreaElement)
           mv <- TA.getValue t
           case mv of 
               Nothing -> return ()
               Just v -> liftIO $ f v

getCarnapDataMap :: Element -> IO (M.Map String String)
getCarnapDataMap elt = do (Just nnmap) <- getAttributes elt
                          len <- NM.getLength nnmap
                          if len > 0 then do
                                mnodes <- mapM (NM.item nnmap) [0 .. len -1]
                                mnamevals <- mapM toNameVal mnodes
                                return $ M.fromList . catMaybes $ mnamevals
                          else return mempty

    where toNameVal (Just node) = do mn <- getNodeName node
                                     mv <- getNodeValue node
                                     case (mn,mv) of
                                         (Just n, Just v) | "data-carnap-" == take 12 n -> return $ Just (Prelude.drop 12 n,v)
                                         _ -> return Nothing
          toNameVal _ = return Nothing

popUpWith :: Element -> Document -> Element -> String -> String -> Maybe String -> IO ()
popUpWith fd w elt label msg details = 
        do setInnerHTML elt (Just label)
           (Just outerpopper) <- createElement w (Just "div")
           (Just innerpopper) <- createElement w (Just "div")
           setAttribute innerpopper "class" "popper"
           setAttribute outerpopper "class" "popperWrapper"
           setInnerHTML innerpopper (Just msg)
           appendChild outerpopper (Just innerpopper)
           case details of 
            Just deets -> do
               (Just detailpopper) <- createElement w (Just "div")
               setAttribute detailpopper "class" "details"
               setInnerHTML detailpopper (Just deets)
               appendChild innerpopper (Just detailpopper)
               return ()
            Nothing -> return ()
           (Just p) <- getParentNode fd
           (Just gp) <- getParentNode p
           appender <- newListener $ appendPopper outerpopper innerpopper gp
           remover <- newListener $ removePopper outerpopper gp
           addListener elt mouseOver appender False
           addListener elt mouseOut remover False
    where appendPopper opop ipop targ = liftIO $ do 
               mtitle <- getAttribute elt "title" :: IO (Maybe String)
               case mtitle of
                   Just s -> do
                       removeAttribute elt "title" 
                       setInnerHTML ipop (Just s)
                   Nothing -> return ()
               appendChild targ (Just opop) 
               makePopper elt opop
          removePopper pop targ = do 
               liftIO $ removeChild targ (Just pop)
               return ()

--------------------------------------------------------
--1.3 Encodings
--------------------------------------------------------

toJSONString :: ToJSON a => a -> JSString
toJSONString = toJSString . decodeUtf8 . BSL.toStrict . encode

decodeHtml :: (StringLike s, Show s) => s -> s
decodeHtml = TS.fromTagText . head . parseTags

decodeJSON :: String -> Maybe Value
decodeJSON = decode . BSL.fromStrict . encodeUtf8 . pack

--reencodes unicode characters in strings that have been mangled by "show"
cleanString :: String -> String
cleanString = concat . map cleanChunk . chunks 
          where chunks s = case break (== '\"') s of 
                                  (l,[]) -> l:[]
                                  (l,_:s') -> l:chunks s'
                cleanChunk c = case (readMaybe $ "\"" ++ c ++ "\"") :: Maybe String of 
                                  Just s -> s
                                  Nothing -> c
                readMaybe s = case reads s of
                                [(x, "")] -> Just x
                                _ -> Nothing

--------------------------------------------------------
--1.4 Optics
--------------------------------------------------------

leaves :: Traversal' (Tree a) (Tree a)
leaves f (T.Node x []) = f (T.Node x [])
leaves f (T.Node x xs) = T.Node <$> pure x <*> traverse (leaves f) xs

adjustFirstMatching :: Traversal' a b -> (b -> Bool) -> (b -> b) -> a -> a
adjustFirstMatching t pred  f x = evalState (traverseOf t adj x) True where
    adj y =  do b <- get
                if b && pred y 
                    then put False >> return (f y)
                    else return y

--------------------------------------------------------
--1.5 Carnap-Specific
--------------------------------------------------------

formToTree :: Plated a => a -> Tree a
formToTree f = T.Node f (map formToTree (children f))

--------------------------------------------------------
--1.6 Boilerplate
--------------------------------------------------------

data ButtonStatus = Edited | Submitted

initElements :: (Document -> HTMLElement -> IO [a]) -> (Document -> a -> IO b) -> IO ()
initElements getter setter = runWebGUI $ \w -> 
            do Just dom <- webViewGetDomDocument w
               Just b <- getBody dom
               elts <- getter dom b
               case elts of 
                    [] -> return ()
                    _ -> mapM_ (setter dom) elts

createSubmitButton :: Document -> Element -> (String -> EventM e MouseEvent ()) -> M.Map String String ->  IO (ButtonStatus -> IO ())
createSubmitButton w bw submit opts = 
      case M.lookup "submission" opts of
         Just s | take 7 s == "saveAs:" -> do
             let l = Prelude.drop 7 s
             bt <- doneButton w "Submit"
             appendChild bw (Just bt)
             submitter <- newListener $ submit l
             addListener bt click submitter False                
             return (setStatus w bt)
         _ -> return (const $ return ())

setStatus w b Edited = setAttribute b "data-carnap-exercise-status" "edited"
setStatus w b Submitted = do dispatchCustom w b "problem-submission"
                             setAttribute b "data-carnap-exercise-status" "submitted"

setSuccess w elt = liftIO (setAttribute elt "class" "success" >> dispatchCustom w elt "exercise-success")

setFailure w elt = liftIO (setAttribute elt "class" "failure" >> dispatchCustom w elt "exercise-failure")

loginCheck callback serverResponse  
     | serverResponse == "submitted!" = callback
     | otherwise = alert serverResponse

errorPopup msg = alert ("Something has gone wrong. Here's the error: " ++ msg)

svgButtonWith :: String -> Document -> String -> IO Element
svgButtonWith svg w thelabel =
            do [Just bt, Just bl, Just cm] <- mapM (createElement w . Just) ["button", "span","span"]
               setInnerHTML bl (Just thelabel)
               setInnerHTML cm (Just svg)
               appendChild bt (Just bl)
               appendChild bt (Just cm)
               return bt

doneButton = svgButtonWith checkSVG 

questionButton = svgButtonWith questionSVG

exclaimButton = svgButtonWith exclaimSVG

expandButton = svgButtonWith expandSVG

createButtonWrapper w o = do (Just bw) <- createElement w (Just "div")
                             setAttribute bw "class" "buttonWrapper"
                             Just par <- getParentNode o
                             appendChild par (Just bw)
                             return bw

--------------------------------------------------------
--1.7 Parsing
--------------------------------------------------------
 
formAndLabel :: Monad m => ParsecT String u m (String, PureForm)
formAndLabel = withLabel (purePropFormulaParser standardLetters <* eof)

seqAndLabel = withLabel (ndParseSeq montagueSCCalc)

folSeqAndLabel =  withLabel (ndParseSeq folCalc)

folFormAndLabel =  withLabel folFormulaParser

withLabel :: Monad m => ParsecT String u m b -> ParsecT String u m (String, b)
withLabel parser = do label <- many (digit <|> char '.')
                      spaces
                      s <- parser
                      return (label,s)

trySubmit w problemType opts ident problemData correct = 
             do msource <- liftIO submissionSource
                key <- liftIO assignmentKey
                case msource of 
                   Nothing -> message "Not able to identify problem source. Perhaps this document has not been assigned?"
                   Just source -> do Just t <- eventCurrentTarget
                                     liftIO $ sendJSON 
                                           (Submit problemType ident problemData source correct 
                                                    (M.lookup "points" opts >>= readMaybe) 
                                                    (M.lookup "late-credit" opts >>= readMaybe) 
                                                    key
                                           ) 
                                           (loginCheck $ (alert $ "Submitted Exercise " ++ ident) >> setStatus w (castToElement t) Submitted)
                                           errorPopup

------------------
--1.8 SVG Data  --
------------------

spinnerSVG = renderHtml [shamlet|
                        <svg version="1.1" id="loader-1" xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" x="0px" y="0px" width="30px" height="30px" viewBox="0 0 40 40" enable-background="new 0 0 40 40" xml:space="preserve">
                            <path opacity="0.2" fill="#000" d="M20.201,5.169c-8.254,0-14.946,6.692-14.946,14.946c0,8.255,6.692,14.946,14.946,14.946 s14.946-6.691,14.946-14.946C35.146,11.861,28.455,5.169,20.201,5.169z M20.201,31.749c-6.425,0-11.634-5.208-11.634-11.634 c0-6.425,5.209-11.634,11.634-11.634c6.425,0,11.633,5.209,11.633,11.634C31.834,26.541,26.626,31.749,20.201,31.749z"/>
                                <path fill="#000" d="M26.013,10.047l1.654-2.866c-2.198-1.272-4.743-2.012-7.466-2.012h0v3.312h0 C22.32,8.481,24.301,9.057,26.013,10.047z">
                                        <animateTransform attributeType="xml" attributeName="transform" type="rotate" from="0 20 20" to="360 20 20" dur="0.5s" repeatCount="indefinite"/>|]

checkSVG = renderHtml [shamlet|
                      <svg version="1.1" viewBox="0 0 120 120" xmlns="http://www.w3.org/2000/svg">
                       <g transform="translate(-46.113 -84.018)">
                         <path d="m106.11 84.018a60 60 0 0 0-60 60 60 60 0 0 0 60 60 60 60 0 0 0 60-60 60 60 0 0 0-60-60zm0 12.095a47.905 47.905 0 0 1 47.905 47.905 47.905 47.905 0 0 1-47.905 47.905 47.905 47.905 0 0 1-47.905-47.905 47.905 47.905 0 0 1 47.905-47.905z"/>
                           <path.filler d="m74.95 141.17 23.653 28.743 38.739-45.778" style="fill:none;stroke-width:15;"/>|]

questionSVG = renderHtml [shamlet|
                            <svg version="1.1" viewBox="0 0 120 120" xmlns="http://www.w3.org/2000/svg">
                             <defs>style="fill:none;stroke-width:15;"/&gt;</defs>
                             <path d="m59.997 0a60 60 0 0 0-60 60 60 60 0 0 0 60 60 60 60 0 0 0 60-60 60 60 0 0 0-60-60zm0 12.095a47.905 47.905 0 0 1 47.905 47.905 47.905 47.905 0 0 1-47.905 47.905 47.905 47.905 0 0 1-47.905-47.905 47.905 47.905 0 0 1 47.905-47.905z"/>
                             <ellipse cx="58.22" cy="92.034" rx="5.339" ry="5.0847" style="fill:none"/>
                             <ellipse.filler cx="59.997" cy="88.865" rx="8.8983" ry="8.1355" style="stroke-width:1.1744"/>
                             <rect.filler x="51.862" y="63.401" width="16.271" height="14.746" ry="0" style="stroke-width:1.0664"/>
                             <path.filler d="m58.942 20.517c-13.969 0.18878-25.496 10.964-26.601 24.864h12.328c1.0506-7.2042 7.1885-12.579 14.482-12.683 8.1481-0.10463 14.858 6.3652 15.034 14.497 0.17565 8.1314-6.2477 14.884-14.393 15.131-2.7817 0.0785-5.1501 0.07525-7.9299 0.07525v11.066c2.6798 0.76758 5.4622 1.1171 8.2489 1.0361 14.841-0.45005 26.544-12.755 26.224-27.571-0.32052-14.817-12.547-26.606-27.394-26.415z" style="stroke-width:.98886"/>|]

expandSVG = renderHtml [shamlet|
                        <svg version="1.1" viewBox="0 0 120 120" xmlns="http://www.w3.org/2000/svg">
                         <defs>style="fill:none;stroke-width:15;"/&gt;</defs>
                         <path d="m0 0v120h120v-120zm14 14h92v92h-92z"/>
                         <g transform="translate(140.64 -.21112)">
                          <rect.filler x="-120.64" y="70.211" width="10" height="30"/>
                          <rect.filler transform="rotate(90)" x="90.211" y="90.642" width="10" height="30"/>
                          <rect.filler transform="rotate(45)" x="-19.447" y="114.1" width="10" height="30"/>
                         <g transform="rotate(90 60.142 59.858)">
                          <g transform="translate(140.64 -.21112)">
                           <rect.filler x="-120.64" y="70.211" width="10" height="30"/>
                           <rect.filler transform="rotate(90)" x="90.211" y="90.642" width="10" height="30"/>
                           <rect.filler transform="rotate(45)" x="-19.447" y="114.1" width="10" height="30"/>
                         <g transform="rotate(180 60.142 59.858)">
                          <g transform="translate(140.64 -.21112)">
                           <rect.filler x="-120.64" y="70.211" width="10" height="30"/>
                           <rect.filler transform="rotate(90)" x="90.211" y="90.642" width="10" height="30"/>
                           <rect.filler transform="rotate(45)" x="-19.447" y="114.1" width="10" height="30"/>
                         <g transform="rotate(-90 60.142 59.858)">
                          <g transform="translate(140.64 -.21112)">
                           <rect.filler x="-120.64" y="70.211" width="10" height="30"/>
                           <rect.filler transform="rotate(90)" x="90.211" y="90.642" width="10" height="30"/>
                           <rect.filler transform="rotate(45)" x="-19.447" y="114.1" width="10" height="30"/>|]

exclaimSVG = renderHtml [shamlet|
                        <svg version="1.1" viewBox="0 0 120 120" xmlns="http://www.w3.org/2000/svg">
                         <defs>style="fill:none;stroke-width:15;"/&gt;</defs>
                         <path d="m59.997 0a60 60 0 0 0-60 60 60 60 0 0 0 60 60 60 60 0 0 0 60-60 60 60 0 0 0-60-60zm0 12.095a47.905 47.905 0 0 1 47.905 47.905 47.905 47.905 0 0 1-47.905 47.905 47.905 47.905 0 0 1-47.905-47.905 47.905 47.905 0 0 1 47.905-47.905z"/>
                         <ellipse cx="58.22" cy="92.034" rx="5.339" ry="5.0847" style="fill:none"/>
                         <ellipse.filler cx="59.997" cy="88.865" rx="8.8983" ry="8.1355" style="stroke-width:1.1744"/>
                         <rect.filler x="51.862" y="25.932" width="16.271" height="47.797" ry="0" style="stroke-width:1.9199"/>|]
                         
--------------------------------------------------------
--2. FFI Wrappers
--------------------------------------------------------

#ifdef __GHCJS__

sendJSON :: ToJSON a => a -> (String -> IO ()) -> (String -> IO ()) -> IO ()
sendJSON x succ fail = do cb1 <- asyncCallback1 (cb succ)
                          cb2 <- asyncCallback3 (cb3 fail)
                          jsonCommand (toJSONString x) cb1 cb2
    where cb f x = do (Just s) <- fromJSVal x 
                      f s
          cb3 f _ x _  = do (Just s) <- fromJSVal x 
                            f s 

genericSendJSON :: ToJSON a => a -> (Value -> IO ()) -> (Value -> IO ()) -> IO ()
genericSendJSON x succ fail = do cb1 <- asyncCallback1 (cb succ)
                                 cb2 <- asyncCallback3 (cb3 fail)
                                 jsonCommand (toJSONString x) cb1 cb2
    where cb f x = do (Just v) <- fromJSVal x 
                      f v
          cb3 f _ x _  = do (Just v) <- fromJSVal x 
                            f v 

keyString :: KeyboardEvent -> IO String
keyString e = key e >>= return . fromJSString

alert :: String -> IO ()
alert = alert' . toJSString

foreign import javascript unsafe "JSON.parse(JSON.stringify($1))" sanatizeJSVal :: JSVal -> IO JSVal

foreign import javascript unsafe "try {jsonCommand($1,$2,$3)} catch(e) {console.log(e)};" jsonCommand :: JSString -> Callback (JSVal -> IO()) -> Callback (JSVal -> JSVal -> JSVal -> IO()) -> IO ()

foreign import javascript unsafe "$1.key" key :: KeyboardEvent -> IO JSString

foreign import javascript unsafe "location.reload()" reloadPage :: IO ()

foreign import javascript unsafe "alert($1)" alert' :: JSString -> IO ()

foreign import javascript unsafe "window.location.href()" currentUrl :: IO JSString

foreign import javascript unsafe "(function(){try {var v=submission_source;} catch (e) {var v=\"no submission source found\";}; return v})()" submissionQueryJS :: IO JSString

foreign import javascript unsafe "(function(){try {var v=assignment_key;} catch (e) {var v=\"\";}; return v})()" assignmentKeyJS :: IO JSString

foreign import javascript unsafe "try {new Popper($1,$2,{placement:\"right\"});} catch (e) {$2.className=\"manualPopper\"};" makePopper :: Element -> Element -> IO ()

foreign import javascript unsafe "window.Carnap = {};" initCallbackObj :: IO ()
--"window.VAR" is apparently best practice for declaring global vars

foreign import javascript unsafe "Carnap[$1]=$2;" initializeCallbackJS :: JSString-> Callback (payload -> succ -> IO ()) -> IO ()
--TODO: unify with other callback code in SequentCheck

foreign import javascript unsafe "$1($2);" simpleCall :: JSVal -> JSVal -> IO ()

submissionSource = do qr <- submissionQueryJS
                      case fromJSString qr of
                          "book" -> return $ Just Book
                          "no submission source found" -> return $ Nothing
                          s | take 11 s == "assignment:" -> return $ Just (Assignment $ Prelude.drop 11 s)
                          _ -> do errorPopup "Bad submission source"; return Nothing

message s = liftIO (alert s)

assignmentKey :: IO String
assignmentKey = do k <- assignmentKeyJS
                   return $ fromJSString k

initialize :: EventName t Event
initialize = EventName $ toJSString "initialize"

mutate :: EventName t Event
mutate = EventName $ toJSString "mutate"

toCleanVal :: JSVal -> IO (Maybe Value)
toCleanVal x = sanatizeJSVal x >>= fromJSVal

initializeCallback :: String -> (Value -> IO Value) -> IO ()
initializeCallback s f = do theCB <- asyncCallback2 (cb f)
                            initializeCallbackJS (toJSString s) theCB
    where cb f jsval onSuccess = do Just val <- toCleanVal jsval
                                    rslt <- f val
                                    rslt' <- toJSVal rslt
                                    simpleCall onSuccess rslt'

#else

initialize :: EventName t Event
initialize = EventName "initialize"

initializeCallback :: (Value -> IO Value) -> IO ()
initializeCallback = error "initializeCallback requires the GHCJS FFI"

toCleanVal :: JSVal -> IO (Maybe Value)
toCleanVal = error "toCleanVal requires the GHCJS FFI"

initCallbackObj :: IO ()
initCallbackObj = error "initCallbackObj requires the GHCJS FFI"

assignmentKey :: IO String
assignmentKey = Prelude.error "assignmentKey requires the GHJS FFI"

submissionSource :: IO (Maybe ProblemSource)
submissionSource = Prelude.error "submissionSource requires the GHCJS FFI"

sendJSON :: ToJSON a => a -> (String -> IO ()) -> (String -> IO ()) -> IO ()
sendJSON = Prelude.error "sendJSON requires the GHCJS FFI"

genericSendJSON :: ToJSON a => a -> (Value -> IO ()) -> (Value -> IO ()) -> IO ()
genericSendJSON = Prelude.error "sendJSON requires the GHCJS FFI"

keyString :: KeyboardEvent -> IO String
keyString = Prelude.error "keyString requires the GHCJS FFI"

alert :: String -> IO ()
alert = Prelude.error "alert requires the GHCJS FFI"

makePopper :: Element -> Element -> IO ()
makePopper = Prelude.error "makePopper requires the GHCJS FFI"

currentUrl = Prelude.error "currentUrl requires the GHCJS FFI"

message s = liftIO (alert s)

reloadPage :: IO ()
reloadPage = Prelude.error "reloadPage requires the GHCJS FFI"

#endif

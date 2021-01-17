module Util.Assignment where

import Import
import Util.Database
import System.Directory (doesFileExist)

getAssignmentByCourse coursetitle filename =
        do mcourse <- runDB $ getBy $ UniqueCourse coursetitle
           case mcourse of
             Nothing -> setMessage ("can't find a class with the title " ++ toHtml coursetitle) >> notFound
             Just c -> retrieveAssignment c filename

-- | given an ident get the director in which assignments are stored for
-- the instructor with that ident
assignmentDir ident = do master <- getYesod
                         return $ (appDataRoot $ appSettings master) </> "documents" </> unpack ident

retrieveAssignment (Entity cid course) filename = do
           alldocs <- runDB $ selectList [DocumentFilename ==. filename] []
           docs <- filterM (creatorAccess cid course) alldocs
           case docs of
                [] -> setMessage ("can't find document record with filename " ++ toHtml filename) >> notFound
                docs -> do
                   let lookup (Entity k doc)= do
                            masgn <- getBy $ UniqueAssignment k cid
                            case masgn of Nothing -> return Nothing; Just asgn -> return (Just (doc,asgn))
                   asgns <- runDB $ catMaybes <$> mapM lookup docs
                   case asgns of
                      [] -> setMessage ("can't find assignment for this course with filename " ++ toHtml filename) >> notFound
                      [(doc,asgn)] -> do
                           maybeIdent <- getIdent (documentCreator doc)
                           case maybeIdent of
                              Just ident -> do
                                 adir <- assignmentDir ident
                                 let path = adir </> unpack filename
                                 exists <- liftIO $ doesFileExist path
                                 if exists then return (asgn, path)
                                           else setMessage ("file not found at " ++ toHtml path) >> notFound
                              Nothing ->
                                 setMessage ("failed to get document creator for " ++ toHtml filename) >> notFound
                      _ -> error "more than one assignment for this course is associated with this filename"
        where creatorAccess cid course (Entity _ doc) = do 
                    mud <- runDB $ getBy $ UniqueUserData (documentCreator doc)
                    case mud >>= userDataInstructorId . entityVal of 
                        Nothing -> return False
                        Just iid | iid == courseInstructor course -> return True
                                 | otherwise -> do mco <- runDB $ getBy (UniqueCoInstructor iid cid)
                                                   return $ not (null mco)

module Util.Assignment where

import           Import
import           System.Directory (doesFileExist)
import           Util.Database

getAssignmentByCourse
    :: Text
    -> Text
    -> Handler (Entity AssignmentMetadata)
getAssignmentByCourse coursetitle title = do
        mcourse <- runDB $ getBy $ UniqueCourse coursetitle
        Entity cid _course <- maybe (setMessage ("can't find a class with the title " ++ toHtml coursetitle) >> notFound) return mcourse
        masgn <- runDB (getBy $ UniqueAssignmentName title cid)
        aent <- maybe (setMessage ("can't find assignment with title  " ++ toHtml title) >> notFound) return masgn
        return aent

getAssignmentAndPathByCourse :: Text -> Text -> Handler (Entity AssignmentMetadata, FilePath)
getAssignmentAndPathByCourse coursetitle title = do
        aent@(Entity _ asgn) <- getAssignmentByCourse coursetitle title
        mdoc <- runDB (get $ assignmentMetadataDocument asgn)
        doc <- maybe (setMessage "can't find the document associated with this assignment" >> notFound) return mdoc
        mident <- getIdent (documentCreator doc)
        ident <- maybe (setMessage "can't find document creator" >> notFound) return mident
        adir <- assignmentDir ident
        let path = adir </> unpack (documentFilename doc)
        exists <- liftIO $ doesFileExist path
        if exists then return (aent, path)
                  else setMessage ("file not found at " ++ toHtml path) >> notFound

-- | given an ident get the director in which assignments are stored for
-- the instructor with that ident
assignmentDir :: Text -> Handler FilePath
assignmentDir ident = do master <- getYesod
                         return $ (appDataRoot $ appSettings master) </> "documents" </> unpack ident

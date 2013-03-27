{-# LANGUAGE TypeOperators, RecordWildCards, MultiParamTypeClasses,
    TemplateHaskell, Rank2Types, LiberalTypeSynonyms, 
    DeriveGeneric, DeriveDataTypeable, FlexibleContexts, KindSignatures #-}
{-
    I am assuming that there is some way to order the edges. This makes sense for planar
    graphs. 

-}
module Language.Graph.Evaluator where
import Data.Graph.Inductive hiding (ap)
import Language.Graph.Types
import Language.Graph.PointedCycle
--import Control.Compose
import Control.Monad.RWS
import Control.Monad.Error hiding (ap)
import Control.Monad.ERWS
--import Data.Functor.Identity
import Data.DList hiding (fromList, head, map, empty, toList)
import Control.Applicative hiding (empty)
import Control.Lens
import Control.Comonad
import Data.Composition
import Data.Maybe
import Data.Tuple.Select
import Data.Tuple.Update
import Data.List
import Data.Data
import GHC.Generics
import Control.Conditional
import Data.Default
import Data.DeriveTH
import Data.Function

-- I am trying to think how to implement undo.
-- the basic idea is that I have a list of commands
-- I have the current state
-- Every command has an inverse
-- when I add a command it updates the state
-- and pushes an undo command on the stack
-- So a command produces an undo

                        
type Env f g a b = ERWST EvalError Config (DList Issue) (GraphContext g a b) f

class (Monad m, Functor m, Applicative m, DynGraph g) => EnvConstraints m g where
                    
eval :: EnvConstraints m g 
     => Operation n e -> Env m g n e ()
eval ( M movement          ) = evalMovement movement
eval ( UpdateEdgeLabel  e  ) = updateEdgeLabel e
eval ( UpdateEdgeTarget i  ) = updateEdgeTarget i
eval ( UpdateNode n        ) = updateNode n
eval ( DeleteNode          ) = deleteNode
eval ( DeleteEdge          ) = deleteEdge
eval ( AddNode n           ) = addNode n
eval ( AddEdge e i         ) = addEdge e i

note :: (Error e, MonadError e m, Monad m) => e -> Maybe a -> m a 
note _ (Just a)  = return a
note err Nothing = throwError err

getOppositeNode :: EnvConstraints m g => Env m g n e Node
getOppositeNode = note EdgeTargetDoesNotExist =<< oppositeNode

updateEdgeLabel :: EnvConstraints m g => e -> Env m g n e ()
updateEdgeLabel e = do
      n <- getCxtNode
      i <- getOppositeNode
      
      cxtGraph . edgeLens n i .= [e]
       
updateEdgeTarget :: EnvConstraints m g => Node -> Env m g n e ()
updateEdgeTarget i = do
    es <- currentEdgeLab
    deleteEdge
    mapM_ (eval . flip AddEdge i) es
        
updateNode :: EnvConstraints m g => n -> Env m g n e ()
updateNode nLab = do
    n <- getCxtNode 
    cxtContext . setJust . cxtNode . _2 .= nLab
    
deleteNode :: EnvConstraints m g => Env m g n e ()
deleteNode = do 
    oppositeNode' <- oppositeNode 
    --if there is no opposite use the first
    nextNode      <- liftM (mplus oppositeNode') $ getFirstNode 
    cxtContext .= Nothing -- this is the actual delete 
    --if there is no first (the graph is empty) do nothing
    maybeM setNodeContext nextNode
    
maybeM :: Monad m => (t -> m ()) -> Maybe t -> m ()
maybeM action (Just x) = action x
maybeM action Nothing  = return ()
    
getFirstNode :: EnvConstraints m g => Env m g n e (Maybe Node)
getFirstNode = do 
    g <- gets _cxtGraph
    
    case nodes g of
        []     -> return Nothing
        (x:xs) -> return $ Just x
    
deleteEdge :: EnvConstraints m g => Env m g n e ()
deleteEdge = do 
    n <- getCxtNode
    i <- getOppositeNode
    
    cxtGraph . edgeLens n i .= [] 

addNode :: EnvConstraints m g => n -> Env m g n e ()
addNode nLab = do
    n <- newNode
    combineContext
    cxtContext .= Just (PointedContext Nothing (n, nLab))

getAsContext :: EnvConstraints m g => Env m g n e (Maybe (Context n e))
getAsContext = do
     cxt <- gets _cxtContext
     let edges = case cxt of
                    Just (PointedContext (Just xs) (n, nLab)) -> Just 
                        (map (snd.toAdj) . filter ((==To) . _direction) $ toList xs, 
                        n,
                        nLab,
                        map (snd.toAdj) . filter ((==From) . _direction) $ toList xs)
                    _ -> Nothing 
     return edges
    
    
combineContext :: EnvConstraints m g => Env m g n e ()
combineContext = do
    --get the context
    g   <- gets _cxtGraph
    --combine it with the graph
    combinedGraph <- maybe g (& g) `liftM` getAsContext 
    --set the graph
    cxtGraph .= combinedGraph
    --set the context to Nothing
    cxtContext .= Nothing
    
addEdge :: EnvConstraints m g => e -> Node -> Env m g n e ()
addEdge e i = do
    n <- getCxtNode
    i <- getOppositeNode
  
    cxtGraph . edgeLens n i .= [e]

getCxtLabNode :: EnvConstraints m g => Env m g n e (LNode n)
getCxtLabNode = do 
    n <- getCxtNode
    g <- gets _cxtGraph 
    let label = case lab g n of
                    Just l  -> l
                    Nothing -> error "logic error! _cxtNodex was not in the graph!"
    return (n, label)
    
getCxtLab :: EnvConstraints m g => Env m g n e n
getCxtLab = liftM snd $ getCxtLabNode

getCxtNode :: EnvConstraints m g => Env m g n e Node
getCxtNode =   note GetNodeOnEmptyGraph 
           =<< gets (fmap (fst . _cxtNode) . _cxtContext)
        
hasEdges :: EnvConstraints m g => Env m g n e Bool
hasEdges = gets (isJust . join . fmap _cxtEdges . _cxtContext )          
      
setJust :: Simple Setter (Maybe a) a         
setJust = sets fmap    
    
evalMovement :: EnvConstraints m g => Movement -> Env m g n e ()
evalMovement IncEdge    = ifM hasEdges 
                                (cxtContext . setJust . cxtEdges . setJust %= inc) $ 
                                tell $ singleton $ W MoveToNonExistantEdge
evalMovement DecEdge    = ifM hasEdges 
                                (cxtContext . setJust . cxtEdges . setJust %= dec) $ 
                                tell $ singleton $ W MoveToNonExistantEdge 
evalMovement FollowEdge = setNodeContext
                        =<< getOppositeNode  

setNodeContext :: EnvConstraints m g => Node -> Env m g n e ()
setNodeContext node = do 
    --the node must be in the graph
    combineContext
    decomp <- gets (match node . _cxtGraph)
    case decomp of 
        (Just cxt, graph) -> do
                                cxtGraph   .= graph
                                cxtContext .= (Just $ cxtToPointedCxt cxt)
        _                 -> throwError SetContextToNoneExistantNode
        
getEdgeNodeList :: (Graph gr) => Node -> gr a b -> PointedCycle Node
getEdgeNodeList n g = fromList $ neighbors g n 

--TODO make this return a maybe and move the error reporting to the commands
oppositeNode :: EnvConstraints m g => Env m g n e (Maybe Node)
oppositeNode = do 
    cxt <- gets (join . fmap _cxtEdges . _cxtContext)
    return $  (_target . extract) <$> cxt

--I might have to check that the node is the next node
nodeLens :: (Graph gr, DynGraph gr) => Node -> Simple Lens (gr a b) a
nodeLens n = result where
    result = lens get set 

    get graph = case match n graph of
        (Just cxt, _) -> sel3 cxt
        _             -> error $ "nodeLens: node " ++ show n ++ " must be in graph"
    
    set g a = case match n g of
        (Just cxt, graph) -> (upd3 a cxt) & graph -- update the context
        _                 -> error $ "nodeLens: node " ++ show n ++ " must be in graph"

--I should probably return an either if the edges are not in the graph
edgeLens :: (Graph gr, DynGraph gr) => Node -> Node -> Simple Lens (gr a b) ([b])
edgeLens start end = result where
    result = lens get set
    
    --TODO have this return 
    get g = case match start g of
        (Just cxt, graph) -> cxt ^. outEdgeContextLens end 
        (Nothing,  graph) -> error $ "Node " ++ show start ++ " is not in graph"
        
    set g labs = case match start g of
        (Just cxt, graph) -> (outEdgeContextLens end .~ labs $ cxt) & graph
        (Nothing,  graph) -> error $ "Node " ++ show start ++ "is not in graph"
    
newNode :: (Graph gr, Monad m) => Env m gr n e Node
newNode = gets $ head . newNodes 1 . _cxtGraph 

currentEdgeLab :: EnvConstraints m gr => Env m gr n e [e]
currentEdgeLab = do
    start <- getCxtNode 
    end   <- getOppositeNode
    use $ cxtGraph . edgeLens start end

outEdgeContextLens :: Node -> Simple Lens (Context a b) ([b])
outEdgeContextLens node = lens get set where
    --get
    get = map fst . filter ((node==) . snd) . sel4
    --set
    set x bs             = upd4 (newPre bs x) x
    newPre bs x          = oldPreMissingEdges x ++ zip bs (repeat node)
    oldPreMissingEdges   = filter ((node/=) . snd) . sel4

swap (x, y) = (y, x)  


decompose :: (Graph gr) => gr a b -> [Context a b]
decompose x = map (context x) $ nodes x

compose :: (Graph gr, DynGraph gr) => [Context a b] -> gr a b
compose xs = foldl' (flip (&)) empty xs










{-# LANGUAGE TypeOperators, TemplateHaskell, Rank2Types, LiberalTypeSynonyms, 
    DeriveGeneric, DeriveDataTypeable, FlexibleContexts #-}
{-
    I am assuming that there is some way to order the edges. This makes sense for planar
    graphs. 

-}
module Language.Graph where
import Data.Graph.Inductive hiding (ap)
import Language.PointedCycle
--import Control.Compose
import Control.Monad.RWS
import Control.Monad.Error hiding (ap)
import Control.Monad.ERWS
--import Data.Functor.Identity
import Data.DList hiding (fromList, head, map, empty)
import Control.Applicative hiding (empty)
import Control.Lens
import Control.Lens.TH
import Control.Comonad
import Data.Composition
import Data.Maybe
import Data.Tuple.Select
import Data.Tuple.Update
import Data.List
import Data.Data
import GHC.Generics
import Control.Conditional


data Config = Config {
        _cfgWrapEdges        :: Bool,
        _deleteNodeWithEdges :: Bool
    }
    deriving(Show, Eq, Read, Ord, Data, Typeable, Generic)

$(makeLenses ''Config)

data Direction = To
               | From
               | Uni
    deriving(Show, Eq, Read, Ord, Data, Typeable, Generic)
    
data DirectedEdge b = DirectedEdge {
        _target    :: Node,
        _edgeValue :: b,
        _direction :: Direction
    }               
    deriving(Show, Eq, Read, Ord, Data, Typeable, Generic)
    
$(makeLenses ''DirectedEdge)

type PointedEdges b = PointedCycle (DirectedEdge b)

-- | tracks a selected in and out adj
data PointedContext a b = PointedContext {
        _cxtEdges :: Maybe (PointedEdges b), -- Is Nothing is there are no edges
        _cxtNode  :: LNode a                
    }
    deriving(Show, Eq, Read, Ord, Data, Typeable, Generic)
    
$(makeLenses ''PointedContext)    
    
data GraphContext g a b = GraphContext {
        _cxtContext    :: Maybe (PointedContext a b), -- Is Nothing if the graph is empty
        _cxtGraph      :: g a b                       -- This is the rest of the graph 
    }
    deriving(Show, Eq, Read, Ord, Generic)

$(makeLenses ''GraphContext)
    
data Movement = IncEdge  
              | DecEdge
              | FollowEdge
    deriving(Show, Eq, Read, Ord, Data, Typeable, Generic)
     
data Operation n e = M Movement
                   | UpdateEdgeLabel  e
                   | UpdateEdgeTarget Int
                   | UpdateNode n
                   | DeleteNode
                   | DeleteEdge
                   | AddNode n
                   | AddEdge e Int
    deriving(Show, Eq, Read, Ord, Data, Typeable, Generic)
                    
data EvalError = EdgeTargetDoesNotExist
               | AddEdgeTargetDoesNotExist 
               | UpdateNodeOnEmptyGraph
               | DeleteNodeOnEmptyGraph
               | GetLabelOnEmptyGraph
               | GetNodeOnEmptyGraph
               | EdgeOperationWithNonexistantEdge
    deriving(Show, Eq, Read, Ord, Data, Typeable, Generic)
               
data Warning = FollowedSelfLoop
             | UpdateEdgeLabelTheSame
             | UpdateEdgeTargetTheSame
             | UpdateNodeTheSame
             | DeleteNodeHasEdges
             | MoveToNonExistantEdge
    deriving(Show, Eq, Read, Ord, Data, Typeable, Generic)
             
data Issue = W Warning

instance (Functor m, Monoid w, Monad m, Error e) => Applicative (ERWST e r w s m) where
    pure  = return
    (<*>) = ap               
    
data Diagnostics = WrappedEdges
    deriving(Show, Eq, Read, Ord, Data, Typeable, Generic)
    
instance Error EvalError 
                        
type Env f g a b = ERWST EvalError Config (DList Issue) (GraphContext g a b) f
                    
eval :: (DynGraph g, Monad m, Functor m) 
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

updateEdgeLabel :: (DynGraph g, Monad m, Functor m) 
                => e -> Env m g n e ()
updateEdgeLabel e = do
      n <- getCxtNode
      i <- oppositeNode 
      
      cxtGraph . edgeLens n i ^= [e]
       
updateEdgeTarget :: (DynGraph g, Monad m, Functor m) 
                 => Node -> Env m g n e ()
updateEdgeTarget i = do
    es <- currentEdgeLab
    deleteEdge
    mapM_ (eval . flip AddEdge i) es
        
updateNode :: (DynGraph g, Monad m) => n -> Env m g n e ()
updateNode nLab = do
    n <- getCxtNode 
    cxtContext . setJust . cxtNode . _2 ^= nLab
    
deleteNode :: (DynGraph g, Monad m) => Env m g n e ()
deleteNode = do
    n <- getCxtNode 
    return $ error "deleteNode"
    --I need to delete and then move on to the next context
    
deleteEdge :: (DynGraph g, Monad m) => Env m g n e ()
deleteEdge = do 
    n <- getCxtNode
    i <- oppositeNode 
    
    cxtGraph . edgeLens n i ^= [] 

addNode :: (DynGraph g, Monad m) => n -> Env m g n e ()
addNode nLab = do
    n <- newNode
    return $ error "addNode"
    
addEdge :: (DynGraph g, Monad m) => e -> Node -> Env m g n e ()
addEdge e i = do
    n <- getCxtNode
    i <- oppositeNode 
  
    cxtGraph . edgeLens n i ^= [e]

getCxtLabNode :: (DynGraph g, Monad m) => Env m g n e (LNode n)
getCxtLabNode = do 
    n <- getCxtNode
    g <- gets _cxtGraph 
    let label = case lab g n of
                    Just l  -> l
                    Nothing -> error "logic error! _cxtNodex was not in the graph!"
    return (n, label)
    
getCxtLab :: (DynGraph g, Monad m) => Env m g n e n
getCxtLab = liftM snd $ getCxtLabNode

getCxtNode :: (DynGraph g, Monad m) => Env m g n e Node
getCxtNode = note GetNodeOnEmptyGraph 
                    =<< gets (fmap (fst . _cxtNode) . _cxtContext)
        
hasEdges :: (Graph g, Monad m) => Env m g n e Bool
hasEdges = gets (isJust . join . fmap _cxtEdges . _cxtContext )          
      
setJust :: Simple Setter (Maybe a) a         
setJust = sets fmap    
    
evalMovement :: (Graph g, Monad m) => Movement -> Env m g n e ()
evalMovement IncEdge    = ifM hasEdges 
                                (cxtContext . setJust . cxtEdges . setJust %= inc) $ 
                                tell $ singleton $ W MoveToNonExistantEdge
evalMovement DecEdge    = ifM hasEdges 
                                (cxtContext . setJust . cxtEdges . setJust %= dec) $ 
                                tell $ singleton $ W MoveToNonExistantEdge 
evalMovement FollowEdge = modify . setNodeContext =<< oppositeNode  

setNodeContext :: (Graph g) => Node -> GraphContext g n e -> GraphContext g n e 
setNodeContext node cxt = error "setNodeContext" --result where
--    cxtEdgeCxt =~= (getEdgeNodeList node $ _cxtGraph cxt) $ cxt

--    result = cxtEdgeCxt =~= $ cxt
        
getEdgeNodeList :: (Graph gr) => Node -> gr a b -> PointedCycle Node
getEdgeNodeList n g = fromList $ neighbors g n 

oppositeNode :: (Graph g, Monad m) => Env m g n e Node
oppositeNode = liftM (_target . extract) $ note EdgeOperationWithNonexistantEdge 
    =<< gets (join . fmap _cxtEdges . _cxtContext)

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
        (Just cxt, graph) -> (outEdgeContextLens end ^~ labs $ cxt) & graph
        (Nothing,  graph) -> error $ "Node " ++ show start ++ "is not in graph"
    
newNode :: (Graph gr, Monad m) => Env m gr n e Node
newNode = gets $ head . newNodes 1 . _cxtGraph 

currentEdgeLab :: (Graph gr, DynGraph gr, Monad m) => Env m gr n e [e]
currentEdgeLab = do
    start <- getCxtNode 
    end   <- oppositeNode
    use $ cxtGraph . edgeLens start end

--inEdgeContextLens :: Node -> Lens (Context a b) ([b])
--inEdgeContextLens node = undefined

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

--nodeContextLens :: Lens (Context a b) (Maybe a)
--nodeContextLens node = undefined









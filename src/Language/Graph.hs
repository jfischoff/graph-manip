{-# LANGUAGE TypeOperators, TemplateHaskell, Rank2Types #-}
{-
    I am assuming that there is some way to order the edges. This makes sense for planar
    graphs. 

-}
module Language.Graph where
import Data.Graph.Inductive
import Language.PointedCycle
--import Control.Compose
import Control.Monad.RWS
import Control.Monad.Error
--import Control.Monad.Trans.Either
--import Data.Functor.Identity
import Data.DList hiding (fromList, head)
--import Control.Applicative
import Lens.Family2
import Lens.Family2.Unchecked
import Lens.Family2.TH
import Control.Monad.ERWS
import Lens.Family2.State.Lazy
import Control.Comonad


data Config = Config {
        _cfgWrapEdges        :: Bool,
        _deleteNodeWithEdges :: Bool
    }

$(mkLenses ''Config)
    
data GraphContext g a b = GraphContext {
        _cxtNode       :: Node,
        _cxtEdgeCxt    :: PointedCycle Node,
        _cxtGraph      :: g a b 
    }

$(mkLenses ''GraphContext)
    
data Movement = IncEdge
              | DecEdge
              | FollowEdge
     
data Operation n e = M Movement
                   | UpdateEdgeLabel  e
                   | UpdateEdgeTarget Int
                   | UpdateNode n
                   | DeleteNode
                   | DeleteEdge
                   | AddNode n
                   | AddEdge e Int
                    
data EvalError = EdgeTargetDoesNotExist
               | AddEdgeTargetDoesNotExist 
               
instance Error EvalError where
    
data Warning = FollowedSelfLoop
             | UpdateEdgeLabelTheSame
             | UpdateEdgeTargetTheSame
             | UpdateNodeTheSame
             | DeleteNodeHasEdges
             
data Issue = W Warning
               
    
data Diagnostics = WrappedEdges
                    
type Env f g a b = ERWST EvalError Config (DList Issue) (GraphContext g a b) f
                    
eval :: (Graph g, Monad m) => Operation n e -> Env m g n e ()
eval ( M movement          ) = evalMovement movement
eval ( UpdateEdgeLabel  e  ) = updateEdgeLabel e
eval ( UpdateEdgeTarget i  ) = updateEdgeTarget i
eval ( UpdateNode n        ) = updateNode n
eval ( DeleteNode          ) = deleteNode
eval ( DeleteEdge          ) = deleteEdge
eval ( AddNode n           ) = addNode n
eval ( AddEdge e i         ) = addEdge e i

updateEdgeLabel :: (Graph g, Monad m) => e -> Env m g n e ()
updateEdgeLabel e = do
    n <- gets _cxtNode
    i <- gets  cxtEdge 
    cxtGraph . edgeLens n i ~= Just e 
    
updateEdgeTarget :: (Graph g, Monad m) => Node -> Env m g n e ()
updateEdgeTarget i = do
    e <- currentEdgeLab
    deleteEdge
    eval $ AddEdge e i
    
updateNode :: (Graph g, Monad m) => n -> Env m g n e ()
updateNode nLab = do
    n <- gets _cxtNode
    cxtGraph . nodeLens n ~= Just nLab
    
deleteNode :: (Graph g, Monad m) => Env m g n e ()
deleteNode = do
    n <- gets _cxtNode
    cxtGraph . nodeLens n ~= Nothing
    
deleteEdge :: (Graph g, Monad m) => Env m g n e ()
deleteEdge = do 
    n <- gets _cxtNode
    i <- gets cxtEdge
    cxtGraph . edgeLens n i ~= Nothing 

addNode :: (Graph g, Monad m) => n -> Env m g n e ()
addNode nLab = do
    n <- newNode
    cxtGraph . nodeLens n ~= Just nLab
    
addEdge :: (Graph g, Monad m) => e -> Node -> Env m g n e ()
addEdge e i = do
    n <- gets _cxtNode
    cxtGraph . edgeLens n i ~= Just e

evalMovement :: (Graph g, Monad m) => Movement -> Env m g n e ()
evalMovement IncEdge    = cxtEdgeCxt %= inc 
evalMovement DecEdge    = cxtEdgeCxt %= dec 
evalMovement FollowEdge = modify . setNodeContext =<< gets oppositeNode  

setNodeContext :: (Graph g) => Node -> GraphContext g n e -> GraphContext g n e 
setNodeContext node cxt = cxtEdgeCxt ^= (getEdgeNodeList node $ _cxtGraph cxt) $ cxt

getEdgeNodeList :: (Graph gr) => Node -> gr a b -> PointedCycle Node
getEdgeNodeList n g = fromList $ neighbors g n 

oppositeNode :: (Graph g) => GraphContext g n e -> Node
oppositeNode = extract . _cxtEdgeCxt

nodeLens :: (Graph gr) => Node -> Lens (gr a b) (Maybe a)
nodeLens = undefined

edgeLens :: (Graph gr) => Node -> Node -> Lens (gr a b) (Maybe b)
edgeLens = undefined

newNode :: (Graph gr, Monad m) => Env m g n e Node
newNode = gets $ head . newNodes 1 . _cxtGraph 

cxtEdge :: GraphContext g a b
cxtEdge = undefined 

currentEdgeLab = undefined


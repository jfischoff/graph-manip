{-# LANGUAGE TypeOperators, RecordWildCards, 
    TemplateHaskell, Rank2Types, LiberalTypeSynonyms, 
    DeriveGeneric, DeriveDataTypeable, FlexibleContexts, KindSignatures #-}
module Language.Graph.Types where
import Data.Default
import Control.Monad.Error
import Data.Data
import GHC.Generics
import Control.Lens
import Control.Lens.TH
import Data.DeriveTH
import Data.Graph.Inductive hiding (ap)
import Language.Graph.PointedCycle

instance Default Bool where
    def = False

data Config = Config {
        _cfgWrapEdges        :: Bool,
        _deleteNodeWithEdges :: Bool
    }
    deriving(Show, Eq, Read, Ord, Data, Typeable, Generic)

$(makeLenses ''Config)
$(derive makeDefault ''Config)

data Direction = To
               | From
               | Uni
    deriving(Show, Eq, Read, Ord, Data, Typeable, Generic)

$(derive makeDefault ''Direction)
    
data DirectedEdge b = DirectedEdge {
        _target    :: Node,
        _edgeValue :: b,
        _direction :: Direction
    }               
    deriving(Show, Eq, Read, Ord, Data, Typeable, Generic)
    
$(makeLenses ''DirectedEdge)
$(derive makeDefault ''DirectedEdge)

toAdj :: DirectedEdge b -> (Direction, (b, Node))
toAdj (DirectedEdge {..}) = (_direction, (_edgeValue, _target))

fromAdj :: Direction -> (b, Node) -> DirectedEdge b
fromAdj dir (b, n) = DirectedEdge n b dir

type PointedEdges b = PointedCycle (DirectedEdge b)

-- | tracks a selected in and out adj
data PointedContext a b = PointedContext {
        _cxtEdges :: Maybe (PointedEdges b), -- Is Nothing is there are no edges
        _cxtNode  :: LNode a                
    }
    deriving(Show, Eq, Read, Ord, Data, Typeable, Generic)
    
cxtToPointedCxt :: Context n e -> PointedContext n e
cxtToPointedCxt (ins, n, nLab, outs) = PointedContext mPointedEdges (n, nLab) where
    mPointedEdges = if null ins && null outs 
                        then Nothing
                        else Just . fromList $ 
                                    map (fromAdj To) ins ++ map (fromAdj From) outs 
                                    
pointedCxtToCxt :: PointedContext n e -> Context n e
pointedCxtToCxt = error "pointedCxtToCxt not implemented"
    
$(makeLenses ''PointedContext) 
$(derive makeDefault ''PointedContext)  
    
data GraphContext g a b = GraphContext {
        _cxtContext    :: Maybe (PointedContext a b), -- Is Nothing if the graph is empty
        _cxtGraph      :: g a b                       -- This is the rest of the graph 
    }
    deriving(Show, Eq, Read, Ord, Generic)

$(makeLenses ''GraphContext)

instance (Default (g a b)) => Default (GraphContext g a b) where
    def = GraphContext def def
    
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
               | SetContextToNoneExistantNode
    deriving(Show, Eq, Read, Ord, Data, Typeable, Generic)
               
data Warning = FollowedSelfLoop
             | UpdateEdgeLabelTheSame
             | UpdateEdgeTargetTheSame
             | UpdateNodeTheSame
             | DeleteNodeHasEdges
             | MoveToNonExistantEdge
    deriving(Show, Eq, Read, Ord, Data, Typeable, Generic)
             
data Issue = W Warning           
    
data Diagnostics = WrappedEdges
    deriving(Show, Eq, Read, Ord, Data, Typeable, Generic)
    
instance Error EvalError
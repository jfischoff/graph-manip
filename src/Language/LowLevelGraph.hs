module Language.LowLevelGraph where
import Data.Graph.Inductive
import Control.Monad.ERWST

data Mutations n e = UpdateEdgeLabel  (LEdge e) e
                   | UpdateEdgeDest   (LEdge e) Int
                   | UpdateEdgeSrc    (LEdge e) Int
                   | UpdateNode       (LNode n)
                   | DeleteNode       Int
                   | DeleteEdge       (LEdge e)
                   | AddNode          (LNode n)
                   | AddEdge          (LEdge e)
                   
type Operation = Mutations

data Issue = IE Error
           | IW Warning
           | ID Diagnostic

data Info = NW Warning
          | ND Diagnostic
           
data Problem = PE Error
             | PW Warning
             
data Error = NodeDoesNotExist      Int
           | EdgeLabelDoesNotExist e
           | EdgeIdsDoNotExist     Int Int

data Warning = UpdateTheSame
             | DeleteNodeHasEdges
             
data Diagnostic


             
type Failure = Report Problem
data Message = Report Info

data Config a = Config {
        cfgTreatAsError  :: [a],
        cfgReport        :: [a],
        cfgSilent        :: Bool,
        cfgReturnContext :: Bool 
    }
    
data Report a = Report a {
        operation :: Operation,
        messages    :: [a]
    }
    
class Report a i where
    messages :: a -> [i]
    
class ErrorConfig m b where
    treatAsError :: b -> m Bool
    log          :: b -> m Bool
    
report :: (ErrorConfig m t, Monad m, MonadReader c m, 
           MonadError (r t) m, Report r t) => r t -> m ()
report issue = do
    reportableMessage <- filterM log $ messages issue
    anyError          <- filterM treatAsError reportableMessage
    let issueToReport = issue { messages = reportableMessage }
    if anyError 
        then throwError issue 
        else when (not $ null anyError) $ tell issue

type Env gr = ERWST Failure Config gr (DList Info)

eval :: DynGraph g => Operation n e -> Env (g a b) ()
eval (UpdateEdgeLabel  edge   e   ) = updateEdgeLabel edge e
eval (UpdateEdgeDest   edge   dst ) = updateEdgeDest  edge dst
eval (UpdateEdgeSrc    edge   src ) = updateEdgeSrc   edge src
eval (UpdateNode       node       ) = updateNode      node    
eval (DeleteNode       nId        ) = deleteNode      nId
eval (DeleteEdge       edge       ) = deleteEdge      edge
eval (AddNode          node       ) = addNode         node
eval (AddEdge          edge       ) = addEdge         edge

updateEdgeLabel :: LEdge e -> e -> Env (g n e) (LEdge e, e)
updateEdgeLabel edge e = do 
    if hasEdge edge
        then deleteEdge edge
        else report (UpdateEdgeLabel edge e) $ edgeIssues edge
        
    newEdge <- insertEdge $ setL label e
    return (newEdge, getL label e)
    
    
updateEdgeDest edge dst = undefined
updateEdgeSrc edge src = undefined
updateNode node = undefined
deleteNode nId = undefined
deleteEdge edge = undefined
addNode node = undefined
addEdge edge = undefined






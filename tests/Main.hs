{-# LANGUAGE TemplateHaskell, QuasiQuotes, RecordWildCards, Rank2Types, 
    NoMonomorphismRestriction, FlexibleContexts, FlexibleInstances,
    TupleSections  #-}
module Main where
import Test.Framework (defaultMain, testGroup, defaultMainWithArgs, Test(..))
import Test.Framework.Providers.HUnit
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.QuickCheck hiding (reason, Result)
import Language.Graph
import qualified Data.Map as M
import Control.Arrow (second)
import Test.HUnit ((@?=), Assertion)
import Data.Graph.Inductive
import Test.QuickCheck.Instances.Tuple
import Test.QuickCheck.Instances.List
import Language.PointedCycle
import Control.Applicative hiding (empty)
import Data.List
import Data.Monoid
import Test.QuickCheck.Property
import Control.Lens

normalizeCxt (i, n, l, o) = (sort i, n, l, sort o) 

normalizeAllCxt = map normalizeCxt . decompose

instance (Eq a, Eq b, Ord a, Ord b) => Eq (Gr a b) where
    x == y = normalizeAllCxt x == normalizeAllCxt y -- eh this will give false positives

instance Arbitrary Direction where
    arbitrary = do
        i <- choose(0, 2 :: Int)
        case i of
            0 -> return To
            1 -> return From
            2 -> return Uni

instance (Arbitrary a, Arbitrary b) => Arbitrary (Gr a b) where
    arbitrary = sized $ \size -> do 
        let nodes = [0..size]
            nGen  = elements nodes
        labNodes <- mapM (\n -> (n,) <$> arbitrary) nodes
        edges <- listOf $ nGen >**< nGen $ arbitrary
        return $ mkGraph labNodes edges     

mkPointedCycle (x:xs) = PointedCycle x xs

pointedCycleArb :: Gen a -> Gen (PointedCycle a)
pointedCycleArb vGen = mkPointedCycle <$> nonEmpty vGen

instance (Arbitrary a) => Arbitrary (DirectedEdge a) where
    arbitrary = directedEdgeArb arbitrary
    
directedEdgeArb :: (Arbitrary a) => Gen Node -> Gen (DirectedEdge a)
directedEdgeArb nGen = DirectedEdge <$> nGen <*> arbitrary <*> arbitrary

instance (Arbitrary a, Arbitrary b) => Arbitrary (PointedContext a b) where
    arbitrary = undefined --pointedContextArb arbitrary
    
maybeGen :: Gen a -> Gen (Maybe a)
maybeGen g = do
    b <- arbitrary
    if b then Just <$> g else return Nothing    

--To this wrong    
pointedContextArb :: (Arbitrary a, Arbitrary b) 
                  => Gen Node 
                  -> (Node -> Maybe (Gen (DirectedEdge b))) -> Gen (PointedContext a b)
pointedContextArb nGen nToEGen = do 
    n <- nGen
    l <- arbitrary
    p <- case nToEGen n of
            Nothing  -> return Nothing
            Just gen -> Just <$> pointedCycleArb gen  
    return $ PointedContext p (n, l)
    
instance (Eq a, Eq b, Arbitrary a, Arbitrary b, Arbitrary (g a b), Graph g) 
    => Arbitrary (GraphContext g a b) where
    arbitrary = do
        graph <- arbitrary
        let nodes' = nodes graph
            
            hasEdgeNode n = result where
                outs = lsuc graph n
                ins  = lpre graph n
                
                justOuts = outs // ins
                justIns  = ins // outs
                unis     = ins `intersect` outs
                
                dirOuts = map (\(i, l) -> DirectedEdge i l To  ) justOuts
                dirIns  = map (\(i, l) -> DirectedEdge i l From) justIns
                dirUnis = map (\(i, l) -> DirectedEdge i l Uni ) unis
                  
                result = case dirOuts ++ dirIns ++ dirUnis of 
                            [] -> Nothing
                            xs -> Just $ elements xs  
            
        pointedContext <- case nodes' of
            [] -> return Nothing
            _  -> Just <$> pointedContextArb (elements nodes') hasEdgeNode
        return $ GraphContext pointedContext graph

main = defaultMain testsToRun

#define TEST_CASE(x) (#x, flip testCase     x)
#define TEST_PROP(x) (#x, flip testProperty x)
#define TEST_CASE_LIST(xs) (zipWith (\i x -> (#xs ++ show i, flip testCase x)) [0..] xs)

data TestConfig = TestConfig {
        includeByDefault :: Bool, 
        overrideGroups   :: [String],
        overrideTests    :: [(String, String)]
    }

allTests :: M.Map String (M.Map String (String -> Test))
allTests = M.fromList $ [
            ("lens properties", M.fromList $ [
                TEST_PROP(propNodeLensIsValidLens          ),
                TEST_PROP(propEdgeLensIsValidLens          ),
                TEST_PROP(propOutEdgeContextLensIsValidLens),
                TEST_PROP(propGrRefl                       ),
                TEST_CASE(testGetSetNodeLens               ),
                TEST_CASE(testSetSetNodeLens               ),
            --]),
            --("arbitraries are valid", M.fromList $ [
                TEST_PROP(propGrArbitraryIsValid   )
                --TEST_PROP(propPointedContextIsValid),
                --TEST_PROP(propGraphContextIsValid  )
            
            ])
            
        ]
         
defaultConfig = TestConfig True [] [] 

testsToRun :: [Test]        
testsToRun = map (uncurry testGroup . second (map (uncurry $ flip ($)) . M.toList)) $ 
                    M.toList $ allTests --filterTests defaultConfig allTests

filterTests :: TestConfig -> M.Map String (M.Map String (String -> Test)) 
               -> M.Map String (M.Map String (String -> Test))
filterTests (TestConfig {..}) = M.filterWithKey (\k _ -> all (/= k) overrideGroups)

instance Monoid Result where
    mempty       = succeeded
    mappend x (MkResult Nothing _ _ _ _ _) = x
    mappend (MkResult Nothing _ _ _ _ _) y = y
    mappend x y = x { 
        ok     = liftA2 (&&) (ok x) (ok y),
        reason = reason x ++ reason y
    }
propGrRefl :: Gr Int Int -> Bool
propGrRefl x = x == x

-- view l (set l b a)  = b        
propSetGetLens :: (Eq b, Show a, Show b) 
               =>  SimpleLens a b -> a -> b -> Result
propSetGetLens l a b = if ((l ^~ b $ a) ^. l) == b 
    then succeeded
    else failed {reason = " propSetGetLens a = " ++ show a ++ ", b = " ++ show b ++ 
                    " (l ^~ b $ a) = " ++ show (l ^~ b $ a) ++ 
                    " (l ^~ b $ a) ^. l " ++ show ((l ^~ b $ a) ^. l)}
--  set l (view l a) a  = a
propGetSetLens :: (Show a, Show b) 
               => (a -> a -> Bool) -> SimpleLens a b -> a -> Result
propGetSetLens eq l a = if (l ^~ (a ^. l) $ a) `eq` a
    then succeeded
    else failed {reason = " propGetSetLens a = " ++ show a ++ 
        " (a ^. l) = " ++ show (a ^. l) ++ 
        " (l ^~ (a ^. l) $ a) = " ++ show (l ^~ (a ^. l) $ a)}
--  set l c (set l b a) = set l c a
propSetSetEqualSet :: (Show a, Show b) 
                   => (a -> a -> Bool) -> SimpleLens a b -> a -> b -> b -> Result
propSetSetEqualSet eq l a b c = if (l ^~ c $ l ^~ b $ a) `eq` (l ^~ c $ a) 
    then succeeded
    else failed {reason = " propSetSetEqualSet: a = " ++ show a ++ ", b = " 
                            ++ show b ++ ", c = " ++ show c }

propIsValidLens :: (Eq b, Show a, Show b)
                => (a -> a -> Bool) -> SimpleLens a b -> a -> b -> b -> Result
propIsValidLens eq l a b c = result where
        sgResult = propSetGetLens l a b
        gsResult = propGetSetLens eq l a 
        ssResult = propSetSetEqualSet eq l a b c
        result = mconcat [sgResult, gsResult, ssResult]
        
propNodeLensIsValidLens :: Gr Int Int -> Int -> Int -> Gen Result 
propNodeLensIsValidLens g a b= do 
    x <- elements $ nodes g
    let result = propIsValidLens (==) (nodeLens x) g a b
    if isBad result
        then return $ result {reason = " propNodeLensIsValidLens x: " ++ show x 
                                ++ reason result}
        else return $ result


propEdgeLensIsValidLens :: Gr Int Int -> [Int] -> [Int] -> Gen Result
propEdgeLensIsValidLens g a b = do 
    x <- elements $ nodes g
    y <- elements $ nodes g
    let result = propIsValidLens (==) (edgeLens x y) g a b
    if isBad result
        then return $ result {reason = " propEdgeLensIsValidLens x: " ++ show x 
                              ++ " y: " ++ show y ++ reason result}
        else return $ result

cxtEq x y = normalizeCxt x == normalizeCxt y

propOutEdgeContextLensIsValidLens :: Context Int Int -> [Int] -> [Int] -> Gen Prop
propOutEdgeContextLensIsValidLens c a b = (not . null $ suc' c) ==> do 
    x <- elements $ suc' c 
    let result = propIsValidLens cxtEq (outEdgeContextLens x) c a b
    if isBad result 
        then return $ result {reason = " propOutEdgeContextLensIsValidLens x: " ++ show x 
                                ++ reason result}
        else return $ result

isBad (MkResult Nothing _ _ _ _ _) = False
isBad (MkResult (Just True) _ _ _ _ _) = False
isBad _ = True

lGetSet :: SimpleLens a b -> a -> a
lGetSet l a = l ^~ (a ^. l) $ a

lSetSet :: SimpleLens a b -> a -> b -> b -> a
lSetSet l a b c = l ^~ c $ l ^~ b $ a

--This fails for a good reason. When I delete the Nodes
-- I also delete the edges
testSetSetNodeLens = actual @?= expected where
    actual = lSetSet (nodeLens 2) graph 1 3
    graph  = compose [
             ([],                0,  1, []), 
             ([],                1, -2, []),
             ([],                2,  2, []),
             ([(-1, 2), (0, 0)], 3,  0, [])] :: Gr Int Int

    expected = (nodeLens 2) ^~ 3 $ graph
    
testGetSetNodeLens = actual @?= expected where
    actual = lGetSet (nodeLens 2) graph 
    graph  = compose [
             ([],                0,  1, []), 
             ([],                1, -2, []),
             ([],                2,  2, []),
             ([(-1, 2), (0, 0)], 3,  0, [])] :: Gr Int Int

    expected = graph

propGrArbitraryIsValid :: Gr Int Int -> Bool
propGrArbitraryIsValid x = show x == show x 

propPointedContextIsValid :: PointedContext Int Int -> Bool
propPointedContextIsValid  = undefined

propGraphContextIsValid :: GraphContext Gr Int Int -> Bool
propGraphContextIsValid    = undefined







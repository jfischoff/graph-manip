module Language.PointedCycle where
import Control.Comonad
import Lens.Family2
import Lens.Family2.Unchecked
import Lens.Family2.TH
import Data.List (tails, inits)
    
data PointedCycle a = PointedCycle a [a] 
    deriving (Eq, Ord, Show, Read)

instance Functor PointedCycle where
    fmap f (PointedCycle x xs) = PointedCycle (f x) $ fmap f xs

instance Comonad PointedCycle where
   extract (PointedCycle x _) = x
   duplicate xxs@(PointedCycle x xs) =
        PointedCycle xxs . fmap listToCycle . tail $ rotations (x:xs)
     where
        rotations :: [a] -> [[a]]
        rotations xs = init $ zipWith (++) (tails xs) (inits xs)
        listToCycle (x:xs) = PointedCycle x xs
        
        
pointedLens :: Lens (PointedCycle a) a
pointedLens = mkLens extract (\(PointedCycle _ y) x -> PointedCycle x y)


inc :: PointedCycle a -> PointedCycle a
inc (PointedCycle x (y:xs)) = PointedCycle y (xs ++ [x])

dec :: PointedCycle a -> PointedCycle a
dec (PointedCycle x xs) = PointedCycle (last xs) (reverse $ tail $ reverse (x:xs))

fromList :: [a] -> PointedCycle a
fromList (x:xs) = PointedCycle x xs

toList :: PointedCycle a -> [a]
toList (PointedCycle x xs) = x:xs

 
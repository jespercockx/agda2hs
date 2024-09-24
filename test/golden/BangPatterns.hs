{-# LANGUAGE BangPatterns #-}
module BangPatterns where

strictId :: a -> a
strictId !x = x

myFoldl :: (b -> a -> b) -> b -> [a] -> b
myFoldl f x0 [] = x0
myFoldl f x0 (x : xs) = myFoldl f (f x0 x) xs

myFoldl' :: (b -> a -> b) -> b -> [a] -> b
myFoldl' f !x0 [] = x0
myFoldl' f !x0 (x : xs) = myFoldl' f (f x0 x) xs

data LazyMaybe a = LazyNothing
                 | LazyJust a

data StrictMaybe a = StrictNothing
                   | StrictJust !a


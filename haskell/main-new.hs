{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}

import Data.Char
import Data.Maybe
import Data.Map as Map
import qualified Data.Text as T
import qualified Data.Array as A

type TParent = (Trie, Char)
data Trie = Trie Bool (Maybe TParent) (Map Char Trie) deriving Eq
instance Show Trie where
  show (Trie hit Nothing m) = "Root Node [" ++ showchild m ++ "]"
    where showchild = Map.foldl (\pre now -> pre ++ " " ++ show now) ""
  show (Trie hit (Just (_,c)) m) = "From :" ++ [c] ++ "[" ++ showchild m ++ "]"
    where showchild = Map.foldl (\pre now -> pre ++ " " ++ show now) ""

realSingleTrie :: Maybe TParent -> String -> Trie
realSingleTrie par [] = Trie True par empty
realSingleTrie par (c:cs) = Trie False par . singleton c $
  realSingleTrie (Just (realSingleTrie par (c:cs), c)) cs

singleTrie :: String -> Trie
singleTrie = realSingleTrie Nothing

getParent :: Trie -> Maybe Trie
getParent (Trie _ Nothing _) = Nothing
getParent (Trie _ (Just (p,_)) _) = Just p

modifyParent :: Maybe TParent -> Trie -> Trie
modifyParent p (Trie hit _ m) = ret
  where
  ret = Trie hit p $
    mapWithKey f m
  f k = modifyParent (Just (ret,k))

realMergeTrie :: Maybe TParent -> Trie -> Trie -> Trie
realMergeTrie par (Trie isA _ ma) (Trie isB _ mb) = ret
  where
  ret = Trie (isA || isB) par $ foldlWithKey f ma mb
  -- self = realMergeTrie par (Trie isA undefined ma) (Trie isB undefined mb)
  f :: Map Char Trie -> Char -> Trie -> Map Char Trie
  f m k b
    | isNothing $ Map.lookup k m = insert k (modifyParent (Just (ret,k)) b) m
    | otherwise = insert k (realMergeTrie (Just (ret, k)) (m ! k) b) m

mergeTrie :: Trie -> Trie -> Trie
mergeTrie = realMergeTrie Nothing

constructTrie :: [String] -> Trie
constructTrie [] = Trie False Nothing empty
constructTrie (x:xs) = mergeTrie (constructTrie xs) (singleTrie x)

getNodeTrie :: String -> Trie -> Maybe Trie
getNodeTrie [] t = Just t
getNodeTrie (c:cs) (Trie _ _ m)
  | isNothing $ Map.lookup c m = Nothing
  | otherwise = getNodeTrie cs $ m ! c

inTrie :: String -> Trie -> Bool
inTrie cs t = maybe False (\(Trie x _ _)->x) (getNodeTrie cs t)

jumpTrie :: Trie -> Char -> Trie
jumpTrie (Trie hit Nothing m) c
  | isNothing $ Map.lookup c m = self
  | otherwise = m ! c
  where
  self = Trie hit Nothing m
jumpTrie (Trie hit par m) c
  | isJust $ Map.lookup c m = m ! c
  | otherwise = jumpTrie (failTrie self) c
  where
  self = Trie hit par m

failTrie :: Trie -> Trie
failTrie (Trie hit Nothing m) = Trie hit Nothing m
failTrie (Trie hit (Just (par, parc)) m)
  | isroot par = par
  | otherwise =  jumpTrie (failTrie par) parc
  where
  isroot (Trie _ p _) = isNothing p

hitfailTrie :: Trie -> Trie
hitfailTrie (Trie hit Nothing m) = Trie hit Nothing m
hitfailTrie (Trie hit (Just (par, parc)) m)
  | isroot par = par
  | ishit $ failTrie self = failTrie self
  | otherwise = hitfailTrie (failTrie self)
  where
  self = Trie hit (Just (par, parc)) m
  isroot (Trie _ p _) = isNothing p
  ishit (Trie h _ _) = h

type AC = Trie

str :: Trie->String
str (Trie _ Nothing _) = []
str (Trie _ (Just (par,c)) _) = str par ++ [c]

buildAC = constructTrie

runAC :: AC -> Char -> AC
runAC a c
  | isJust $ Map.lookup c sub = sub ! c
  | isroot a = a
  | otherwise = runAC (failTrie a) c
    where
    Trie _ _ sub = a
    isroot (Trie _ p _) = isNothing p

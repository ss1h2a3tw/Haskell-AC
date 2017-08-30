{-# LANGUAGE LambdaCase #-}

import Control.Monad.State.Lazy
import Data.Maybe
import qualified Data.Map as M
import Control.Applicative

data TrieNode = TrieNode Bool (Maybe (Char,Int)) Int (M.Map Char Int) deriving (Show,Eq)
data Trie = Trie (M.Map Int TrieNode) Int deriving (Show,Eq)

addChild :: Int -> Char -> Bool -> State Trie Int
addChild idx c hit = modify f >> gets (\(Trie _ len) -> len-1)
  where
    f (Trie m len) = Trie (g m len) (len+1)
    g m len = M.insert len (TrieNode hit (Just (c,idx)) (-1) M.empty) m'
      where
      m' = M.adjust k idx m
      k (TrieNode h p f cm) = TrieNode h p f $
        M.insert c len cm

getIdx :: String -> State Trie (Maybe Int)
getIdx s = gets $ \(Trie m _) -> run m 0 s
  where
    run m idx [] = Just idx
    run m idx (c:cs)
      | isNothing $ M.lookup idx m = Nothing
      | isNothing $ M.lookup c cm = Nothing
      | otherwise = run m (cm M.! c) cs
        where
          TrieNode _ _ _ cm = m M.! idx

getNode :: Int -> State Trie (Maybe TrieNode)
getNode idx = gets $ \(Trie m _) -> M.lookup idx m

adjustNode :: Int -> (TrieNode -> TrieNode) -> State Trie ()
adjustNode idx g = modify f
  where
    f (Trie m x) = Trie (M.adjust g idx m) x

isExist :: String -> State Trie Bool
isExist s = fmap isJust (getIdx s)

isHit :: String -> State Trie Bool
isHit s =
  do
    midx <- getIdx s
    Trie m len <- get
    return $ f midx m
  where
    f Nothing _ = False
    f (Just idx) m = hit
      where
        TrieNode hit _ _ _ = m M.! idx

-- return the added index

addString :: String -> State Trie Int
addString s = realAddString s 0

realAddString :: String -> Int -> State Trie Int
realAddString [] idx =
  do
    adjustNode idx markHit
    return idx
  where
    markHit (TrieNode _ par fail m) = TrieNode True par fail m

realAddString (c:cs) idx =
  do
    (TrieNode _ _ _ m) <- fromJust <$> getNode idx
    f m
  where
    f m
      | isNothing $ M.lookup c m =
        do
          idx' <- addChild idx c False
          realAddString cs idx'
      | otherwise = realAddString cs $ fromJust $ M.lookup c m

addStrings :: [String] -> State Trie ()
addStrings ss = forM_ ss addString

--Expect the nodes which idx smaller then self is calculated
calFail :: Int -> State Trie ()
calFail 0 = adjustNode 0 $ \(TrieNode hit par _ m) -> TrieNode hit par 0 m
calFail idx = getNode idx >>= \case
  Just (TrieNode _ (Just (_, 0)) _ _) ->
    adjustNode idx $ setFail 0
  Just tn@(TrieNode _ (Just (c, x)) _ _) ->
    getNode x >>= \case
      Just pn@(TrieNode _ _ f _) -> do
        fail' <- runFail f c
        getNode fail' >>= \case
          Just (TrieNode _ _ _ m) ->
            adjustNode idx . setFail $ fromMaybe fail' (M.lookup c m)
  where
    setFail i (TrieNode hit par _ m) = TrieNode hit par i m

--try to get the node that have child with char
runFail :: Int -> Char -> State Trie Int
runFail 0 c = return 0
runFail idx c =
  do
    TrieNode _ _ fail m <- fromJust <$> getNode idx
    if isJust (M.lookup c m)
      then return idx
      else runFail fail c

--The actual running states in AC
runAC :: Char -> Int -> State Trie Int
runAC c idx =
  do
    TrieNode _ _ _ m <- fromJust <$> getNode idx
    if isJust (M.lookup c m)
      then return $ fromJust $ M.lookup c m
      else do
        fail <- runFail idx c
        TrieNode _ _ _ m' <- fromJust <$> getNode fail
        return $ fromMaybe fail $ M.lookup c m'

getString :: Int -> State Trie String
getString idx =
  do
    TrieNode _ par _ _ <- fromJust <$> getNode idx
    if isNothing par
      then return []
      else do
        s <- getString (pari par)
        return $ s++[parc par]
  where
    parc (Just (x,_)) = x
    pari (Just (_,x)) = x

isHitIdx :: Int -> State Trie Bool
isHitIdx idx =
  do
    (TrieNode h _ _ _) <- fromJust <$> getNode idx
    return h

--little helper
scanrM m i [] = return [i]
scanrM m i (x:xs) =
  do
    j <- m x i
    js <- scanrM m j xs
    return (i:js)

nullTrie = Trie (M.singleton 0 (TrieNode False Nothing (-1) M.empty)) 1

runtest = runState test nullTrie
test =
  do
    addStrings ["a","ab","bab","bc","bca","c","caa"]
    (Trie _ len) <- get
    forM_ [0..(len-1)] calFail
    r <- scanrM runAC 0 "abccab"
    s <- mapM getString r
    h <- mapM isHitIdx r
    return (r,s,h)
{-
test2 = forM ["a","ab","abc","b","ba","bc","bcc","z"] isHit

test3 = test >> test2
-}

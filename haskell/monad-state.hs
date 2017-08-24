import Control.Monad.State.Lazy
import Data.Maybe
import qualified Data.Map as M

data TrieNode = TrieNode Bool (Maybe (Char,Int)) Int (M.Map Char Int) deriving (Show,Eq)
data Trie = Trie (M.Map Int TrieNode) Int deriving (Show,Eq)

addChild :: Int -> Char -> Bool -> State Trie Int
addChild idx c hit =
  do
    t <- get
    put $ f t
    return (getlen (f t) -1)
  where
  getlen (Trie _ l) = l
  f (Trie m len) = Trie (g m len) (len+1)
  g m len = M.insert len (TrieNode hit (Just (c,idx)) (-1) (M.empty)) m'
    where
    m' = M.adjust k idx m
    k (TrieNode h p f cm) = TrieNode h p f $
      M.insert c len cm

getIdx :: String -> State Trie (Maybe Int)
getIdx s = gets f
  where
    f (Trie m _) = run m 0 s
    run m idx [] = Just idx
    run m idx (c:cs)
      | isNothing $ M.lookup idx m = Nothing
      | isNothing $ M.lookup c cm = Nothing
      | otherwise = run m (cm M.! c) cs
        where
          TrieNode _ _ _ cm = m M.! idx

getNode :: Int -> State Trie (Maybe TrieNode)
getNode idx = gets f
  where
    f (Trie m _) = M.lookup idx m

adjustNode :: Int -> (TrieNode -> TrieNode) -> State Trie ()
adjustNode idx g = modify f
  where
    f (Trie m x) = Trie (M.adjust g idx m) x

isExist :: String -> State Trie Bool
isExist s = liftM isJust (getIdx s)

isHit :: String -> State Trie Bool
isHit s =
  do
    midx <- (getIdx s)
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
    adjustNode idx (markHit)
    return idx
  where
    markHit (TrieNode _ par fail m) = (TrieNode True par fail m)

realAddString (c:cs) idx =
  do
    (TrieNode _ _ _ m) <- liftM fromJust $ getNode idx
    f m
  where
    f m
      | isNothing $ M.lookup c m =
        do
          idx' <- addChild idx c False
          realAddString cs idx'
      | otherwise =
        do
          realAddString cs $ fromJust $ M.lookup c m

addStrings :: [String] -> State Trie ()
addStrings ss = forM_ ss addString

--Expect the nodes which idx smaller then self is calculated
calFail :: Int -> State Trie ()
calFail 0 =
  do
    adjustNode 0 f
  where
    f (TrieNode hit par _ m) = TrieNode hit par 0 m
calFail idx =
  do
    tn <- liftM fromJust $ getNode idx
    if (par tn) == 0
      then adjustNode idx $ setfail 0
      else do
        pn <- liftM fromJust $ getNode $ par tn
        fail' <- runFail (fail pn) (parc tn)
        TrieNode _ _ _ m <- liftM fromJust $ getNode fail'
        if isNothing (M.lookup (parc tn) m)
          then adjustNode idx $ setfail fail'
          else adjustNode idx $ setfail $ fromJust $ M.lookup (parc tn) m
  where
    fail (TrieNode _ _ f _) = f
    par (TrieNode _ (Just (_,x)) _ _ ) = x
    parc (TrieNode _ (Just (c,_)) _ _) = c
    setfail i (TrieNode hit par _ m) = TrieNode hit par i m

--try to get the node that have child with char
runFail :: Int -> Char -> State Trie (Int)
runFail 0 c = return 0
runFail idx c =
  do
    TrieNode _ _ fail m <- liftM fromJust $ getNode idx
    if isJust (M.lookup c m)
      then return idx
      else runFail fail c

--The actual running states in AC
runAC :: Char -> Int -> State Trie (Int)
runAC c idx =
  do
    TrieNode _ _ _ m <- liftM fromJust $ getNode idx
    if isJust (M.lookup c m)
      then return $ fromJust $ M.lookup c m
      else do
        fail <- runFail idx c
        TrieNode _ _ _ m' <- liftM fromJust $ getNode fail
        if isJust (M.lookup c m')
          then return $ fromJust $ M.lookup c m'
          else return fail

nullTrie = Trie (M.singleton 0 (TrieNode False Nothing (-1) M.empty)) 1

test =
  do
    put nullTrie
    addStrings ["abc","ab","ba","bcc"]
    (Trie _ len) <- get
    forM_ [0..(len-1)] calFail
    a0 <- runAC 'a' 0
    a1 <- runAC 'b' a0
    a2 <- runAC 'c' a1
    a3 <- runAC 'c' a2
    return a3
{-
test2 = forM ["a","ab","abc","b","ba","bc","bcc","z"] isHit

test3 = test >> test2
-}

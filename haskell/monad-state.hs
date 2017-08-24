import Control.Monad.State.Lazy
import Data.Maybe
import qualified Data.Map as M

data TrieNode = TrieNode Bool (Maybe Int) Int (M.Map Char Int) deriving (Show,Eq)
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
  g m len = M.insert len (TrieNode hit (Just idx) (-1) (M.empty)) m'
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

nullTrie = Trie (M.singleton 0 (TrieNode False Nothing 0 M.empty)) 1

test =
  do
    put nullTrie
    addStrings ["abc","ab","ba","bcc"]
    return ()
test2 = forM ["a","ab","abc","b","ba","bc","bcc","z"] isHit

test3 = test >> test2

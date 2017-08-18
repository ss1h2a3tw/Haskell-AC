import Control.Monad.State.Lazy
import Data.Maybe
import qualified Data.Map as M

data TrieNode = TrieNode Bool (Maybe Int) (M.Map Char Int) deriving (Show,Eq)
data Trie = Trie (M.Map Int TrieNode) Int deriving (Show,Eq)

-- addchild :: Int -> Char ->
addChild :: Int -> Char -> Bool -> State Trie Int
addChild idx c hit =
  do
    t <- get
    put $ f t
    return (getlen (f t) -1)
  where
  getlen (Trie _ l) = l
  f (Trie m len) = Trie (g m len) (len+1)
  g m len= M.insert len (TrieNode hit (Just idx) (M.empty)) m'
    where
    m' = M.adjust k idx m
    k (TrieNode h p cm) = TrieNode h p $
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
          TrieNode _ _ cm = m M.! idx

getNode :: Int -> State Trie (Maybe TrieNode)
getNode idx = gets f
  where
    f (Trie m _) = M.lookup idx m

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
        TrieNode hit _ _ = m M.! idx

nullTrie = Trie (M.singleton 0 (TrieNode False Nothing M.empty)) 1

test :: State Trie (Bool)
test =
  do
    put nullTrie
    addChild 0 'a' True
    isHit "b"

import qualified Data.Map as M

data TrieNode = TrieNode Bool (Maybe Int) (M.Map Char Int) deriving (Show,Eq)
data Trie a = Trie (M.Map Int TrieNode) [(Int,TrieNode)] a deriving (Show,Eq)

instance Functor Trie where
  fmap f (Trie x y a) = Trie x y (f a)

instance Applicative Trie where
  pure = Trie M.empty []
  (Trie ax ay f) <*> (Trie bx by b) = Trie bx by (f b)

instance Monad Trie where
  return = pure
  (Trie x _ a) >>= f = Trie newx [] b
    where
    Trie _ mods b = f a
    newx = runmod mods x
    runmod [] ma = ma
    runmod ((id,dat):ms) ma = M.insert id dat $ runmod ms ma

insertTrie i a = Trie M.empty [(i,a)] ()

test = insertTrie 0 (TrieNode False Nothing M.empty)

{-
getID
-}


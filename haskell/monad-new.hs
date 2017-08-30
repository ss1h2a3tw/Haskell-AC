import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe

data TrieNode = TrieNode Bool (Maybe Int) (M.Map Char Int) deriving (Show,Eq)
data Trie a = Trie (M.Map Int TrieNode) (Either [(String,TrieNode)] String) a deriving (Show,Eq)

instance Functor Trie where
  fmap f (Trie x y a) = Trie x y (f a)

root = TrieNode False Nothing M.empty

instance Applicative Trie where
  pure = Trie (M.singleton 0 root) (Left [])
  (Trie ax ay f) <*> (Trie bx by b) = Trie bx by (f b)

minNotInMapIdx m = S.findMin $ S.map succ ks S.\\ ks
  where
    ks = M.keysSet m

strToIdx [] _ _ = 0
--Assumption: all the chars except end in trie
strToIdx [c] idx m
  | isNothing (M.lookup c current) = minNotInMapIdx m
  | otherwise = fromJust $ M.lookup c current
  where TrieNode _ _ current = m M.! idx
strToIdx (c:cs) idx m = strToIdx cs (fromJust $ M.lookup c current) m
  where TrieNode _ _ current = m M.! idx


instance Monad Trie where
  return = pure
--for getID
{-
  (Trie x (Right query) a) >>= f = Trie x (Left []) a >>= f
    where
    res = strToIdx query 0 x
-}
  (Trie x (Left _) a) >>= f = Trie newx (Left []) b
    where
    Trie _ op origb = f a
    isQuery = isRight op
    b
      | isQuery = strToIdx (fromRight op) 0 x
      | otherwise = origb
    newx
      | isQuery = x
      | otherwise = runmod mods x
    runmod [] ma = ma
    runmod ((str,dat):ms) ma = M.insert (strToIdx str 0 ret) dat ret
      where ret = runmod ms ma

{-
insertTrie i a = Trie M.empty [(i,a)] ()
test = do
  insertTrie 0 (TrieNode False Nothing M.empty)

getID
-}


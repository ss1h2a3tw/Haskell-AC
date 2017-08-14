import Data.Char
import Data.Maybe
data Trie = Trie Bool [Trie] | TNull deriving (Show,Eq)

singleTrie [] = Trie True [TNull | x <- [0..127]]
singleTrie (c:cs) = Trie False [ sel x | x<-[0..127] ] where
    sel x
        | x == (ord c) = singleTrie cs
        | otherwise = TNull

mergeTrie TNull x = x
mergeTrie x TNull = x
mergeTrie (Trie isA as) (Trie isB bs) = Trie (isA || isB) $ zipWith mergeTrie as bs

constructTrie [] = Trie False [ TNull | x<-[0..127] ]
constructTrie (x:xs) = mergeTrie (constructTrie xs) (singleTrie x)

getnodeTrie _ TNull = Nothing
getnodeTrie [] t = Just t
getnodeTrie (c:cs) (Trie _ ts) = getnodeTrie cs $ ts!!(ord c)

inTrie cs t = isHit where
    isHit
        | Nothing == getnodeTrie cs t = False
        | otherwise =  (\(Trie x _)->x) $ fromJust $ getnodeTrie cs t

jumpTrie [] c (Trie _ ts)
    | ts!!(ord c) == TNull = []
    | otherwise = [c]
jumpTrie cs c t
    | ts!!(ord c) /= TNull = cs++[c]
    | otherwise = jumpTrie (failTrie cs t) c t
    where (Trie _ ts) = fromJust $ getnodeTrie cs t

failTrie [] _ = []
failTrie (x:[]) _ = []
failTrie xs t = jumpTrie pre (last xs) t where
    pre = failTrie (init xs) t

hitfailTrie [] _ = []
hitfailTrie (x:[]) _ = []
hitfailTrie xs t
    | isHit = res
    | otherwise = failTrie res t where
        res = failTrie xs t
        Trie isHit _ = fromJust $ getnodeTrie res t


data AC = AC {
  isroot :: Bool
, str :: String
, failAC :: AC
, hitfailAC :: AC
, hit :: Bool
, sub :: [AC]
} | ANull deriving (Show,Eq)


realbuildAC cs root =  AC (cs==[]) cs (realbuildAC (failTrie cs root) root) (realbuildAC (hitfailTrie cs root) root) isHit buildsub where
    (Trie isHit ts) = fromJust $ getnodeTrie cs root
    buildsub = [sel x|x<-[0..127]]
    sel x
        | ts!!x == TNull = ANull
        | otherwise = realbuildAC (cs++[chr x]) root

buildAC ss = realbuildAC [] $ constructTrie ss

runAC a c
    | (sub a)!!(ord c) == ANull = if (isroot a) then a else (runAC (failAC a) c)
    | otherwise = (sub a)!!(ord c)


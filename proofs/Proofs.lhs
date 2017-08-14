\documentclass{article}

%if False
\begin{code}
import Data.List
import Control.Arrow
\end{code}
%endif

\usepackage{amsmath}
\usepackage{amsthm}

%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt

%include Formatting.fmt

%let showproofs = True

\newtheorem{theorem}{Theorem}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}

\begin{document}

\title{Derivation of Aho-Corasick Algorithm: Notes}
\author{Shen-Huei Chen and Shin-Cheng Mu}
\date{}

\maketitle

\paragraph{Specification} Assume functions |inits, tails :: [a] -> {[a]}|
and overload functions such as |map| and |concat|, etc, to sets. Define
\begin{code}
subs :: [a] -> [([a],[a])]
subs = concat . map (distl . fork tails id) . inits {-"~~."-}
\end{code}
The problem can be specified by:
\begin{code}
search :: Eq a => [[a]] -> [a] -> [([a],[a])]
search p = filter ((`elem` p) . fst) . subs {-"~~."-}
\end{code}
%if False
\begin{code}
distl :: ([a], b) -> [(a,b)]
distl (xs, y) = map (\x -> (x,y)) xs

fork :: (a -> b) -> (a -> c) -> a -> (b, c)
fork = (&&&)

snoc :: [a] -> a -> [a]
snoc xs x = xs ++ [x]
\end{code}
%endif

\paragraph{Routine calculation} We calculate
\begin{spec}
   filter ((`elem` p) . fst) . subs
=   {- definition -}
   filter ((`elem` p) . fst) . concat . map (distl . fork tails id) . inits
=   {- |filter p . concat = concat . map (filter p)|, |map| fusion -}
   concat . map (filter ((`elem` p) . fst) . distl . (fork tails id)) . inits
=   {- naturalty laws -}
   concat . map (distl . fork (filter (`elem` p) . tails) id) . inits {-"~~."-}
\end{spec}
We denote |distl . (fork (filter (`elem` p) . tails) id)| by |searchTail|.

For brevity, we denote |xs ++ [x]| by |xs `snoc` x|. Apparently, |fork inits id| can be written as a |foldl|:
\begin{spec}
fork inits id = foldl odot ([[]], []) {-"~~,"-}
  where (xss, xs) `odot` x = (xss `union` [xs `snoc` x], xs `snoc` x) {-"~~."-}
\end{spec}

Abbreviate |concat . map (distl . fork (filter (`elem` p) . tails) id)| to |h|. We have
\begin{spec}
   (h *** id) . (fork inits id)
=   {- property above -}
   (h *** id) . foldl odot ([[]], [])
=   {- |foldl| fusion -}
   foldl oplus (searchTail [], []) {-"~~,"-}
\end{spec}
where |(yss, ys) `oplus` x = (yss `union` searchTail (xs `snoc` x), xs `snoc` x)|.
The fusion is justified by
\begin{spec}
   (h *** id) ((xss, xs) `odot` x)
=    {- definition of |odot| -}
   (h *** id) (xss `union` [xs `snoc` x], xs `snoc` x)
=    {- definition of |***| -}
   (h (xss `union` [xs `snoc` x]), xs `snoc` x)
=    {- definition of |h|, properties of |concat| and |map| -}
   (h xss `union` searchTail (xs `snoc` x), xs `snoc` x)
=    {- define |(yss, ys) `oplus` x = (yss `union` searchTail (xs `snoc` x), xs `snoc` x)| -}
   ((h *** id) (xss, xs)) `oplus` x {-"~~."-}
\end{spec}
Thus we currently have:
\begin{spec}
  search p = fst . foldl oplus (searchTail [], []) {-"~~,"-}
    where  (yss, ys) `oplus` x = (yss `union` searchTail (xs `snoc` x), xs `snoc` x)
           searchTail = distl . fork (filter (`elem` p) . tails) id {-"~~."-}
\end{spec}

\paragraph{Generalisation and Refinement} We generalise |searchTail| to
\begin{spec}
  searchTail p q = distl . fork (filter (`elem` p) . filter (`elem` q) . tails) id {-"~~."-}
\end{spec}
By some argument yet to be formally proved, we have that if we define |lms| (for ``longest matching suffix'') to be:
\begin{spec}
lms = maxlen . filter (`elem` q) . tails {-"~~,"-}
\end{spec}
provided that |[] `elem` q|, we have that
\begin{spec}
 filter (`elem` q) . tails = filter (`elem` q) . tails . lms {-"~~,"-}
\end{spec}
\begin{spec}
searchTail p q = distl . fork (filter (`elem` p) . filter (`elem` q) . tails . lms) id{-"~~."-}
\end{spec}
\end{document}

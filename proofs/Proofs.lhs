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

\newcommand{\todo}[1]{{\bf ToDo}: \{#1\}}
\begin{document}

\title{Derivation of Aho-Corasick Algorithm: Notes}
\author{Shen-Huei Chen and Shin-Cheng Mu}
\date{}

\maketitle

\paragraph{Specification} Assume functions |inits, tails :: [a] -> {[a]}|,
|distl :: (Set a, b) -> Set (a,b)|, and overload functions such as |map| and
|concat|, etc, to sets. Define
\begin{code}
subs :: [a] -> Set ([a],[a])
subs = concat . map (distl . fork tails id) . inits {-"~~."-}
\end{code}
The problem can be specified by:
\begin{code}
search :: Eq a => {[a]} -> [a] -> {([a],[a])}
search ps = filter ((`elem` ps) . fst) . subs {-"~~."-}
\end{code}
%if False
\begin{code}
type Set a = [a]

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
   filter ((`elem` ps) . fst) . subs
=   {- definition -}
   filter ((`elem` ps) . fst) . concat . map (distl . fork tails id) . inits
=   {- |filter p . concat = concat . map (filter p)|, |map| fusion -}
   concat . map (filter ((`elem` ps) . fst) . distl . (fork tails id)) . inits
=   {- naturalty laws -}
   concat . map (distl . fork (filter (`elem` ps) . tails) id) . inits {-"~~."-}
\end{spec}
We denote |distl . (fork (filter (`elem` ps) . tails) id)| by |searchTail|.

For brevity, we denote |xs ++ [x]| by |xs `snoc` x|. Apparently, |fork inits id| can be written as a |foldl|:
\begin{spec}
fork inits id = foldl odot ({[]}, []) {-"~~,"-}
  where (xss, xs) `odot` x = (xss `union` [xs `snoc` x], xs `snoc` x) {-"~~."-}
\end{spec}

Abbreviate |concat . map (distl . fork (filter (`elem` p) . tails) id)| to |h|. We have
\begin{spec}
   (h *** id) . (fork inits id)
=   {- property above -}
   (h *** id) . foldl odot ({[]}, [])
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
  search ps = fst . foldl oplus (searchTail [], []) {-"~~,"-}
    where  (yss, ys) `oplus` x = (yss `union` searchTail (xs `snoc` x), xs `snoc` x)
           searchTail = distl . fork (filter (`elem` ps) . tails) id {-"~~."-}
\end{spec}
The main algorithm is molded into a |foldl|. We have yet to find an efficient way
to compute |searchTail|, however.

\paragraph{Generalisation and Refinement} We generalise |searchTail| to
\begin{spec}
  searchTail ps qs = distl . fork (filter (`elem` ps) . filter (`elem` qs) . tails) id {-"~~."-}
\end{spec}
By some argument yet to be formally proved, if we define |lms| (for ``longest matching suffix'') to be:
\begin{spec}
lms qs = maxlen . filter (`elem` qs) . tails {-"~~,"-}
\end{spec}
provided that |[] `elem` qs|, we have that
\begin{equation}
 |filter (`elem` qs) . tails = filter (`elem` qs) . tails . lms qs| \label{eq:filtTailsLms}
\end{equation}
which gives us
\begin{spec}
searchTail ps qs = distl . fork (filter (`elem` ps) . filter (`elem` qs) . tails . lms qs) id{-"~~."-}
\end{spec}
\todo{More details arguing for \eqref{eq:filtTailsLms}.}

\todo{I am not sure the functional notation below is better than the set-theoretical
notation presented in the van Geldrop paper. Anyway, let's try.}

The next wish is to turn |lms| into a |foldl|. Here we need the assumption that
|q| is prefix closed. For prefix closed |q|, we have
\begin{equation}
  |filter (`elem` qs) . map (`snoc` x) = filter (`elem` qs) . filter (`elem` map (`snoc` x) qs) . map (`snoc` x)| \label{eq:filter-prefix-closed}
\end{equation}
And we also have that for all |q|:
\begin{equation}
  |filter (`elem` map (`snoc` x) qs) . map (`snoc` x) = map (`snoc` x) .  filter (`elem` qs)|
    \label{eq:filter-snoc}
\end{equation}

We reason:
\begin{spec}
   lms qs (xs `snoc` x)
=    {- definition of |lms| -}
   maxlen (filter (`elem` qs) (tails (xs `snoc` x)))
=    {- definition of |tails| -}
   maxlen (filter (`elem` qs) (map (`snoc` x) (tails xs) `union` set []))
=    {- |filter| distributes into |union|, |[] `elem` q| -}
   maxlen (filter (`elem` qs) (map (`snoc` x) (tails xs)) `union` set []) {-"~~."-}
\end{spec}
Focuse on the inner expression:
\begin{spec}
   filter (`elem` qs) (map (`snoc` x) (tails xs))
=    {- |q| prefix closed, \eqref{eq:filter-prefix-closed} -}
   filter (`elem` qs) (filter (`elem` map (`snoc` x) qs) (map (`snoc` x) (tails xs)))
=    {- by \eqref{eq:filter-snoc} -}
   filter (`elem` qs) (map (`snoc` x) (filter (`elem` qs) (tails xs)))
=    {- by \eqref{eq:filtTailsLms} -}
   filter (`elem` qs) (map (`snoc` x) (filter (`elem` qs) (tails (lms qs xs))))
=    {- calculation backwards -}
   filter (`elem` qs) (map (`snoc` x) (tails (lms qs xs))) {-"~~."-}
\end{spec}
Back to the main expression:
\begin{spec}
   lms qs (xs `snoc` x)
=    {- calculation above -}
   maxlen (filter (`elem` qs) (map (`snoc` x) (tails (lms qs xs))) `union` set [])
=    {- |[] `elem` q|, definition of |tails|, etc -}
   maxlen (filter (`elem` qs) (tails (map (`snoc` x) (lms qs xs))))
=    {- definition of |lms| -}
   lms qs (map (`snoc` x) (lms qs xs)) {-"~~."-}
\end{spec}
Therefore we have that |lms qs| is a |foldl|:
\begin{spec}
lms qs []             = []
lms qs (xs `snoc` x)  = lms qs (map (`snoc` x) (lms qs xs)) {-"~~."-}
\end{spec}

\paragraph{Tupling} Now that |lms| is also a |foldl|, it can be computed together
with |search| to speed up the computation. Define
\begin{spec}
search3 ps qs xs = (search ps xs, xs, lms qs xs) {-"~~."-}
\end{spec}
Standard calculation gives us that
\begin{spec}
search3 ps qs = foldl otimes (searchTail [], [], []) {-"~~,"-}
  where  (xss, xs, ys) `otimes` x = (xss `union` searchTail' (zs, xs `snoc` x), xs `snoc` x, zs) {-"~~,"-}
           where  zs = lms qs (ys `snoc` x)
                  searchTail' = distl . (filter (`elem` ps) . filter (`elem` qs) . tails *** id) {-"~~."-}
\end{spec}
This completes the functional derivation of the Aho-Corasick algorithm. What remains is to compute |lms| and |searchTail'| quickly using data structure.
\end{document}

module Games

import public Games.TypeTrees

namespace Continuation
  parameters {R : Type}
    public export
    K : Type -> Type
    K x = (x -> R) -> R

namespace Continuation
  public export
  data 𝓚 : {r : Type} -> Tree -> Type where
    Nil : 𝓚 []
    (::) : K {R = r} x -> ((u : x) -> 𝓚 {r} (xf u)) ->
      𝓚 {r} (x :: xf)
parameters {0 R : Type}
  public export
  sub : (DPair x y -> R) -> (u : x) -> y u -> R
  sub q u us = q (u ** us)

  infix 6 .*.
  public export
  (.*.) : forall y . K {R} x -> ((u : x) ->
    K {R} (y u)) -> K {R} (DPair x y)
  (phi .*. gamma) q = phi (\u => gamma u (sub q u))

  public export
  Ksequence : 𝓚 {r = R} xt -> K {R} (Path xt)
  Ksequence [] = \q => q []
  Ksequence (phi :: phif) =
    -- TODO: Clean this up
    \q =>
    let w =
         phi .*. (\u => Ksequence (phif u))
    in w (\case (v ** vs) => q (v :: vs))

  -- Skip monad structure of K
  record Game where
    constructor MkGame
    Xt : Tree
    q : Path Xt -> R
    phit : 𝓚 {r = R} Xt

  optimalOutcome : Game -> R
  optimalOutcome game = Ksequence game.phit game.q

namespace Strategy
  -- Again, take advantage of Type : Type
  public export
  data Strategy : Tree -> Type where
    Nil : Strategy []
    (::) : x  ->  -- What to do if I need to make a move here
           ((u : x) -> Strategy (xf u)
            -- What to do if I need to make a move there
           ) -> Strategy (x :: xf)

path : Strategy xt -> Path xt
path [] = []
path (x :: sigmaf) = x :: path (sigmaf x)

namespace Selection
  parameters {R : Type}
    public export
    J : Type -> Type
    J x = (x -> R) -> x

    public export
    data 𝓙 : Tree -> Type where
      Nil : 𝓙 []
      (::) : J x -> ((u : x) -> 𝓙 (xf u)) -> 𝓙 (x :: xf)

  parameters {0 R : Type}
    public export
    (.*.) : forall y . J {R} x -> ((u : x) -> J {R} (y u)) ->
      J {R} (DPair x y)
    epsilon .*. delta = \q =>
      let b = \x => delta x (sub q x)
          a = epsilon (\u => q (u ** b u ))
      in (a ** b a)

    Jsequence : 𝓙 {R} xt -> J {R} (Path xt)
    Jsequence [] = \q => []
    Jsequence (epsilon :: epsilonf) = \q =>
      -- TODO: clean up
      let w = epsilon .*. (\u => Jsequence $ epsilonf u)
          (r ** rs) = w (\(s ** ss) => q (s :: ss))
      in (r :: rs)

    -- Skip monadic code

    selectionStrategy : 𝓙 {R} xt -> (Path xt -> R) -> Strategy xt
    selectionStrategy [] q = []
    selectionStrategy {xt = x :: xf}
      epsilont@(epsilon :: epsilonf) q =
      u0 :: sigmaf
      where
        u0 : x
        u0 = head (Jsequence epsilont q)

        sigmaf : (u : x) -> Strategy (xf u)
        sigmaf u = selectionStrategy (epsilonf u)
                     (q . (u ::))

    overline : J {R} x -> K {R} x
    overline epsilon = \p => p (epsilon p)

    Overline : 𝓙 {R} xt -> 𝓚 {r = R} xt
    Overline [] = []
    Overline (epsilon :: epsilonf) = overline epsilon ::
      (\u => Overline (epsilonf u))

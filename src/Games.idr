module Games

import public Games.TypeTrees

namespace Continuation
  parameters {R : Type}
    public export
    K : Type -> Type
    K x = (x -> R) -> R

    public export
    data 𝓚 : Tree -> Type where
      Nil : 𝓚 []
      (::) : K x -> ((u : x) -> 𝓚 (xf u)) -> 𝓚 (x :: xf)
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
  Ksequence : 𝓚 {R} xt -> K {R} (Path xt)
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
    phit : 𝓚 {R} Xt

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

    Jsequence : 𝓙 {R} xt -> J (Path xt)
    Jsequence [] = \q => []
    Jsequence (epsilon :: epsilonf) = \q =>
      let w = epsilon .*. (\u => Jsequence $ epsilonf u)
      in ?h1

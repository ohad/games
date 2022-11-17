module Games.TypeTrees

namespace Tree
  public export
  data Tree : Type where
    Nil : Tree
    (::) : (X : Type) -> (Xf : X -> Tree) -> Tree

public export
Path : Tree -> Type
Path [] = ()
Path (x :: xf) = DPair x (Path . xf)

namespace Path
  public export
  Nil : Path []
  Nil = ()

  public export
  (::) : (u : x) -> Path (xf u) -> Path (x :: xf)
  (::) = MkDPair

public export
head : Path (x :: xf) -> x
head = (.fst)

-- Bug https://github.com/idris-lang/Idris2/issues/2777
public export
tail : (p : Path (x :: xf)) -> Path (xf p.fst)
tail = (.snd)

public export
length : {tree : Tree} -> Path tree -> Nat
length {tree =   []   } p = 0
length {tree = x :: xf} (u ** us) = S (TypeTrees.length us)

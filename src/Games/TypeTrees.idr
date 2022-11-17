module Games.TypeTrees

namespace Tree
  public export
  data Tree : Type where
    Nil : Tree
    (::) : (X : Type) -> (Xf : X -> Tree) -> Tree

namespace Path
  -- Take advantage of Type : Type
  public export
  data Path : Tree -> Type where
    Nil : Path []
    (::) : (u : x) -> Path (xf u) -> Path (x :: xf)

public export
head : Path (x :: xf) -> x
head (u :: us) = u

-- Bug https://github.com/idris-lang/Idris2/issues/2777
public export
tail : (p : Path (x :: xf)) -> Path (xf (head p))
tail (u :: us) = us

public export
length : Path tree -> Nat
length [] = 0
length (u :: us) = S (TypeTrees.length us)

structure Graph (V : Type) where
  addjList : V → List V

namespace Graph

def createEmptyGraph (V : Type) : Graph V :=
  -- {addjList := λ _ => []}
  Graph.mk (λ _ => [])

def addEdge {V : type} (g : Graph V) (v1 v2 : V) : Graph V :=
  {
    addjList := λ v =>

  }

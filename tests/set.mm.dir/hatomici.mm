include "chshii.mm"
include "shatomici.mm"

theorem hatomici
  let vx: setvar x
  let cA: class A
  assume hatomic.1: |- A e. CH

  disjoint A x
  assert |- ( A =/= 0H -> E. x e. HAtoms x C_ A )

  proof
    vx
    cA
    cA
    hatomic.1
    chshii
    shatomici
end

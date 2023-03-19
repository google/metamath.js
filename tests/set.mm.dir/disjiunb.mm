include "ciun.mm"
include "weq.mm"
include "iuneq12d.mm"
include "disjor.mm"

theorem disjiunb
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vi: setvar i
  let vj: setvar j
  let cE: class E
  assume disjiunb.1: |- ( i = j -> B = D )
  assume disjiunb.2: |- ( i = j -> C = E )

  disjoint A i
  disjoint A j
  disjoint i j
  disjoint B j
  disjoint B x
  disjoint j x
  disjoint C j
  disjoint E i
  disjoint D i
  disjoint D x
  disjoint i x
  assert |- ( Disj_ i e. A U_ x e. B C <-> A. i e. A A. j e. A ( i = j \/ ( U_ x e. B C i^i U_ x e. D E ) = (/) ) )

  proof
    cA
    vx
    cB
    cC
    ciun
    vx
    cD
    cE
    ciun
    vi
    vj
    vi
    vj
    weq
    vx
    cB
    cD
    cC
    cE
    disjiunb.1
    disjiunb.2
    iuneq12d
    disjor
end

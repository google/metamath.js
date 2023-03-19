include "cvv.mm"
include "wcel.mm"
include "ciun.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cuni.mm"
include "dfiun2g.mm"
include "a1i.mm"
include "mprg.mm"

theorem dfiun2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume dfiun2.1: |- B e. _V

  disjoint x y
  disjoint A y
  disjoint B y
  assert |- U_ x e. A B = U. { y | E. x e. A y = B }

  proof
    cB
    cvv
    wcel
    #
    vx
    cA
    cB
    ciun
    vy
    cv
    cB
    wceq
    vx
    cA
    wrex
    vy
    cab
    cuni
    wceq
    vx
    cA
    vx
    vy
    cA
    cB
    cvv
    dfiun2g
    @0
    vx
    cv
    cA
    wcel
    dfiun2.1
    a1i
    mprg
end

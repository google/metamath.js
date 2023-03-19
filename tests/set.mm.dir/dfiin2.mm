include "cvv.mm"
include "wcel.mm"
include "ciin.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cint.mm"
include "dfiin2g.mm"
include "a1i.mm"
include "mprg.mm"

theorem dfiin2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume dfiun2.1: |- B e. _V

  disjoint x y
  disjoint A y
  disjoint B y
  assert |- |^|_ x e. A B = |^| { y | E. x e. A y = B }

  proof
    cB
    cvv
    wcel
    #
    vx
    cA
    cB
    ciin
    vy
    cv
    cB
    wceq
    vx
    cA
    wrex
    vy
    cab
    cint
    wceq
    vx
    cA
    vx
    vy
    cA
    cB
    cvv
    dfiin2g
    @0
    vx
    cv
    cA
    wcel
    dfiun2.1
    a1i
    mprg
end

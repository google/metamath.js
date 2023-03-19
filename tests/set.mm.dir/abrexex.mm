include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "abrexexg.mm"
include "ax-mp.mm"

theorem abrexex
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume abrexex.1: |- A e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  assert |- { y | E. x e. A y = B } e. _V

  proof
    cA
    cvv
    wcel
    vy
    cv
    cB
    wceq
    vx
    cA
    wrex
    vy
    cab
    cvv
    wcel
    abrexex.1
    vx
    vy
    cA
    cB
    cvv
    abrexexg
    ax-mp
end

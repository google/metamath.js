include "cvv.mm"
include "ciin.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "cab.mm"
include "wal.mm"
include "df-iin.mm"
include "ralv.mm"
include "abbii.mm"
include "eqtri.mm"

theorem viin
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A y
  assert |- |^|_ x e. _V A = { y | A. x y e. A }

  proof
    vx
    cvv
    cA
    ciin
    vy
    cv
    cA
    wcel
    #
    vx
    cvv
    wral
    #
    vy
    cab
    @0
    vx
    wal
    #
    vy
    cab
    vx
    vy
    cvv
    cA
    df-iin
    @1
    @2
    vy
    @0
    vx
    ralv
    abbii
    eqtri
end

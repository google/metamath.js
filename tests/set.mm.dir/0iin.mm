include "c0.mm"
include "ciin.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "cab.mm"
include "cvv.mm"
include "df-iin.mm"
include "vex.mm"
include "ral0.mm"
include "2th.mm"
include "abbi2i.mm"
include "eqtr4i.mm"

theorem 0iin
  let vx: setvar x
  let cA: class A
  let vy: setvar y


  assert |- |^|_ x e. (/) A = _V

  proof
    vx
    c0
    cA
    ciin
    vy
    cv
    #
    cA
    wcel
    #
    vx
    c0
    wral
    #
    vy
    cab
    cvv
    vx
    vy
    c0
    cA
    df-iin
    @2
    vy
    cvv
    @0
    cvv
    wcel
    @2
    vy
    vex
    @1
    vx
    ral0
    2th
    abbi2i
    eqtr4i
end

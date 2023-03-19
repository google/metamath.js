include "wcel.mm"
include "cqs.mm"
include "cv.mm"
include "cec.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cvv.mm"
include "df-qs.mm"
include "abrexexg.mm"
include "syl5eqel.mm"

theorem qsexg
  let cA: class A
  let cR: class R
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. V -> ( A /. R ) e. _V )

  proof
    cA
    cV
    wcel
    cA
    cR
    cqs
    vy
    cv
    vx
    cv
    cR
    cec
    #
    wceq
    vx
    cA
    wrex
    vy
    cab
    cvv
    vx
    vy
    cA
    cR
    df-qs
    vx
    vy
    cA
    @0
    cV
    abrexexg
    syl5eqel
end

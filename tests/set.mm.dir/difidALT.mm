include "cdif.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "crab.mm"
include "c0.mm"
include "dfdif2.mm"
include "dfnul3.mm"
include "eqtr4i.mm"

theorem difidALT
  let cA: class A
  let vx: setvar x


  assert |- ( A \ A ) = (/)

  proof
    cA
    cA
    cdif
    vx
    cv
    cA
    wcel
    wn
    vx
    cA
    crab
    c0
    vx
    cA
    cA
    dfdif2
    vx
    cA
    dfnul3
    eqtr4i
end

include "wor.mm"
include "wpo.mm"
include "cv.mm"
include "wbr.mm"
include "weq.mm"
include "w3o.mm"
include "wral.mm"
include "df-so.mm"
include "simplbi.mm"

theorem sopo
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( R Or A -> R Po A )

  proof
    cA
    cR
    wor
    cA
    cR
    wpo
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    vx
    vy
    weq
    @1
    @0
    cR
    wbr
    w3o
    vy
    cA
    wral
    vx
    cA
    wral
    vx
    vy
    cA
    cR
    df-so
    simplbi
end

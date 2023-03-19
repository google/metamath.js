include "c0.mm"
include "wor.mm"
include "wpo.mm"
include "cv.mm"
include "wbr.mm"
include "weq.mm"
include "w3o.mm"
include "wral.mm"
include "po0.mm"
include "ral0.mm"
include "df-so.mm"
include "mpbir2an.mm"

theorem so0
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- R Or (/)

  proof
    c0
    cR
    wor
    c0
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
    c0
    wral
    #
    vx
    c0
    wral
    cR
    po0
    @2
    vx
    ral0
    vx
    vy
    c0
    cR
    df-so
    mpbir2an
end

include "con0.mm"
include "cha.mm"
include "cin.mm"
include "c1o.mm"
include "c2o.mm"
include "cpr.mm"
include "ct1.mm"
include "wss.mm"
include "cv.mm"
include "haust1.mm"
include "ssriv.mm"
include "sslin.mm"
include "ax-mp.mm"
include "onint1.mm"
include "sseqtri.mm"
include "ssoninhaus.mm"
include "eqssi.mm"

theorem oninhaus
  let vx: setvar x


  assert |- ( On i^i Haus ) = { 1o , 2o }

  proof
    con0
    cha
    cin
    #
    c1o
    c2o
    cpr
    #
    @0
    con0
    ct1
    cin
    #
    @1
    cha
    ct1
    wss
    @0
    @2
    wss
    vx
    cha
    ct1
    vx
    cv
    haust1
    ssriv
    cha
    ct1
    con0
    sslin
    ax-mp
    onint1
    sseqtri
    ssoninhaus
    eqssi
end

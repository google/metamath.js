include "con0.mm"
include "cep.mm"
include "wfr.mm"
include "cv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "dfepfr.mm"
include "simpr.mm"
include "wel.mm"
include "wex.mm"
include "n0.mm"
include "wn.mm"
include "onfrALTlem1.mm"
include "expd.mm"
include "onfrALTlem2.mm"
include "pm2.61.mm"
include "syl6c.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "mpd.mm"
include "mpgbir.mm"

theorem onfrALT
  let va: setvar a
  let vx: setvar x
  let vy: setvar y


  assert |- _E Fr On

  proof
    con0
    cep
    wfr
    va
    cv
    #
    con0
    wss
    #
    @0
    c0
    wne
    #
    wa
    #
    @0
    vy
    cv
    cin
    c0
    wceq
    vy
    @0
    wrex
    #
    wi
    va
    va
    vy
    con0
    dfepfr
    @3
    @2
    @4
    @1
    @2
    simpr
    @2
    vx
    va
    wel
    #
    vx
    wex
    @3
    @4
    vx
    @0
    n0
    @3
    @5
    @4
    vx
    @3
    @5
    @0
    vx
    cv
    cin
    c0
    wceq
    #
    @4
    wi
    @6
    wn
    #
    @4
    wi
    @4
    @3
    @5
    @6
    @4
    vx
    vy
    va
    onfrALTlem1
    expd
    @3
    @5
    @7
    @4
    vx
    vy
    va
    onfrALTlem2
    expd
    @6
    @4
    pm2.61
    syl6c
    exlimdv
    syl5bi
    mpd
    mpgbir
end

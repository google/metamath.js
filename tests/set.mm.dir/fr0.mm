include "c0.mm"
include "wfr.mm"
include "cv.mm"
include "wss.mm"
include "wne.mm"
include "wa.mm"
include "wbr.mm"
include "crab.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "dffr2.mm"
include "wn.mm"
include "ss0.mm"
include "a1d.mm"
include "necon1ad.mm"
include "imp.mm"
include "mpgbir.mm"

theorem fr0
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- R Fr (/)

  proof
    c0
    cR
    wfr
    vx
    cv
    #
    c0
    wss
    #
    @0
    c0
    wne
    #
    wa
    vz
    cv
    vy
    cv
    cR
    wbr
    vz
    @0
    crab
    c0
    wceq
    vy
    @0
    wrex
    #
    wi
    vx
    vx
    vy
    vz
    c0
    cR
    dffr2
    @1
    @2
    @3
    @1
    @3
    @0
    c0
    @1
    @0
    c0
    wceq
    @3
    wn
    @0
    ss0
    a1d
    necon1ad
    imp
    mpgbir
end

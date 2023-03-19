include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "csb.mm"
include "cv.mm"
include "wsbc.mm"
include "cab.mm"
include "c0.mm"
include "df-csb.mm"
include "wfal.mm"
include "sbcex.mm"
include "con3i.mm"
include "pm2.21d.mm"
include "falim.mm"
include "impbid1.mm"
include "abbidv.mm"
include "fal.mm"
include "abf.mm"
include "syl6eq.mm"
include "syl5eq.mm"

theorem csbprcOLD
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y


  assert |- ( -. A e. _V -> [_ A / x ]_ B = (/) )

  proof
    cA
    cvv
    wcel
    #
    wn
    #
    vx
    cA
    cB
    csb
    vy
    cv
    cB
    wcel
    #
    vx
    cA
    wsbc
    #
    vy
    cab
    #
    c0
    vx
    vy
    cA
    cB
    df-csb
    @1
    @4
    wfal
    vy
    cab
    c0
    @1
    @3
    wfal
    vy
    @1
    @3
    wfal
    @1
    @3
    wfal
    @3
    @0
    @2
    vx
    cA
    sbcex
    con3i
    pm2.21d
    @3
    falim
    impbid1
    abbidv
    wfal
    vy
    fal
    abf
    syl6eq
    syl5eq
end

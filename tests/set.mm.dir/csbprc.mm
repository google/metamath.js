include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "cv.mm"
include "wsbc.mm"
include "cab.mm"
include "wfal.mm"
include "csb.mm"
include "c0.mm"
include "sbcex.mm"
include "falim.mm"
include "pm5.21ni.mm"
include "abbidv.mm"
include "df-csb.mm"
include "fal.mm"
include "abf.mm"
include "eqcomi.mm"
include "3eqtr4g.mm"

theorem csbprc
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
    wfal
    vy
    cab
    #
    vx
    cA
    cB
    csb
    c0
    @1
    @3
    wfal
    vy
    @3
    @0
    wfal
    @2
    vx
    cA
    sbcex
    @0
    falim
    pm5.21ni
    abbidv
    vx
    vy
    cA
    cB
    df-csb
    @4
    c0
    wfal
    vy
    fal
    abf
    eqcomi
    3eqtr4g
end

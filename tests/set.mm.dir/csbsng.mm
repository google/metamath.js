include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "cab.mm"
include "csb.mm"
include "csn.mm"
include "wsbc.mm"
include "csbab.mm"
include "sbceq2g.mm"
include "abbidv.mm"
include "syl5eq.mm"
include "df-sn.mm"
include "csbeq2i.mm"
include "3eqtr4g.mm"

theorem csbsng
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vy: setvar y


  assert |- ( A e. V -> [_ A / x ]_ { B } = { [_ A / x ]_ B } )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    vy
    cv
    #
    cB
    wceq
    #
    vy
    cab
    #
    csb
    #
    @1
    vx
    cA
    cB
    csb
    #
    wceq
    #
    vy
    cab
    #
    vx
    cA
    cB
    csn
    #
    csb
    @5
    csn
    @0
    @4
    @2
    vx
    cA
    wsbc
    #
    vy
    cab
    @7
    @2
    vx
    vy
    cA
    csbab
    @0
    @9
    @6
    vy
    vx
    cA
    @1
    cB
    cV
    sbceq2g
    abbidv
    syl5eq
    vx
    cA
    @8
    @3
    vy
    cB
    df-sn
    csbeq2i
    vy
    @5
    df-sn
    3eqtr4g
end

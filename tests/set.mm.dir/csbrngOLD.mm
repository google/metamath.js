include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wex.mm"
include "cab.mm"
include "csb.mm"
include "crn.mm"
include "wsbc.mm"
include "csbab.mm"
include "sbcex2.mm"
include "wb.mm"
include "sbcel2.mm"
include "a1i.mm"
include "exbidv.mm"
include "syl5bb.mm"
include "abbidv.mm"
include "syl5eq.mm"
include "dfrn3.mm"
include "csbeq2i.mm"
include "3eqtr4g.mm"

theorem csbrngOLD
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vw: setvar w
  let vy: setvar y


  assert |- ( A e. V -> [_ A / x ]_ ran B = ran [_ A / x ]_ B )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    vw
    cv
    vy
    cv
    cop
    #
    cB
    wcel
    #
    vw
    wex
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
    wcel
    #
    vw
    wex
    #
    vy
    cab
    #
    vx
    cA
    cB
    crn
    #
    csb
    @6
    crn
    @0
    @5
    @3
    vx
    cA
    wsbc
    #
    vy
    cab
    @9
    @3
    vx
    vy
    cA
    csbab
    @0
    @11
    @8
    vy
    @11
    @2
    vx
    cA
    wsbc
    #
    vw
    wex
    @0
    @8
    @2
    vw
    vx
    cA
    sbcex2
    @0
    @12
    @7
    vw
    @12
    @7
    wb
    @0
    vx
    cA
    @1
    cB
    sbcel2
    a1i
    exbidv
    syl5bb
    abbidv
    syl5eq
    vx
    cA
    @10
    @4
    vw
    vy
    cB
    dfrn3
    csbeq2i
    vw
    vy
    @6
    dfrn3
    3eqtr4g
end

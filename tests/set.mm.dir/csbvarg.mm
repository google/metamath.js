include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "csb.mm"
include "wceq.mm"
include "elex.mm"
include "wsbc.mm"
include "cab.mm"
include "vex.mm"
include "df-csb.mm"
include "sbcel2gv.mm"
include "abbi1dv.mm"
include "syl5eq.mm"
include "ax-mp.mm"
include "csbeq2i.mm"
include "csbco.mm"
include "3eqtr3i.mm"
include "syl.mm"

theorem csbvarg
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. V -> [_ A / x ]_ x = A )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    #
    vx
    cA
    vx
    cv
    #
    csb
    #
    cA
    wceq
    cA
    cV
    elex
    @0
    @2
    vz
    cv
    #
    vy
    cv
    #
    wcel
    vy
    cA
    wsbc
    #
    vz
    cab
    #
    cA
    vy
    cA
    vx
    @4
    @1
    csb
    #
    csb
    vy
    cA
    @4
    csb
    @2
    @6
    vy
    cA
    @7
    @4
    @4
    cvv
    wcel
    #
    @7
    @4
    wceq
    vy
    vex
    @8
    @7
    @3
    @1
    wcel
    vx
    @4
    wsbc
    #
    vz
    cab
    @4
    vx
    vz
    @4
    @1
    df-csb
    @8
    @9
    vz
    @4
    vx
    @3
    @4
    cvv
    sbcel2gv
    abbi1dv
    syl5eq
    ax-mp
    csbeq2i
    vx
    vy
    cA
    @1
    csbco
    vy
    vz
    cA
    @4
    df-csb
    3eqtr3i
    @0
    @5
    vz
    cA
    vy
    @3
    cA
    cvv
    sbcel2gv
    abbi1dv
    syl5eq
    syl
end

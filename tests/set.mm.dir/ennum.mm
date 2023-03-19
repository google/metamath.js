include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "con0.mm"
include "wrex.mm"
include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "enen2.mm"
include "rexbidv.mm"
include "isnum2.mm"
include "3bitr4g.mm"

theorem ennum
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A ~~ B -> ( A e. dom card <-> B e. dom card ) )

  proof
    cA
    cB
    cen
    wbr
    #
    vx
    cv
    #
    cA
    cen
    wbr
    #
    vx
    con0
    wrex
    @1
    cB
    cen
    wbr
    #
    vx
    con0
    wrex
    cA
    ccrd
    cdm
    #
    wcel
    cB
    @4
    wcel
    @0
    @2
    @3
    vx
    con0
    cA
    cB
    @1
    enen2
    rexbidv
    vx
    cA
    isnum2
    vx
    cB
    isnum2
    3bitr4g
end

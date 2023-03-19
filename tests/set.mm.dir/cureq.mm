include "wceq.mm"
include "cdm.mm"
include "cv.mm"
include "cop.mm"
include "wbr.mm"
include "copab.mm"
include "cmpt.mm"
include "ccur.mm"
include "dmeq.mm"
include "dmeqd.mm"
include "breq.mm"
include "opabbidv.mm"
include "mpteq12dv.mm"
include "df-cur.mm"
include "3eqtr4g.mm"

theorem cureq
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A = B -> curry A = curry B )

  proof
    cA
    cB
    wceq
    #
    vx
    cA
    cdm
    #
    cdm
    #
    vx
    cv
    vy
    cv
    cop
    #
    vz
    cv
    #
    cA
    wbr
    #
    vy
    vz
    copab
    #
    cmpt
    vx
    cB
    cdm
    #
    cdm
    #
    @3
    @4
    cB
    wbr
    #
    vy
    vz
    copab
    #
    cmpt
    cA
    ccur
    cB
    ccur
    @0
    vx
    @2
    @6
    @8
    @10
    @0
    @1
    @7
    cA
    cB
    dmeq
    dmeqd
    @0
    @5
    @9
    vy
    vz
    @3
    @4
    cA
    cB
    breq
    opabbidv
    mpteq12dv
    vx
    vy
    vz
    cA
    df-cur
    vx
    vy
    vz
    cB
    df-cur
    3eqtr4g
end

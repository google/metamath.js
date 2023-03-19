include "cch.mm"
include "chil.mm"
include "cv.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "cort.mm"
include "cfv.mm"
include "wrex.mm"
include "crio.mm"
include "cmpt.mm"
include "cpjh.mm"
include "ax-hilex.mm"
include "mptex.mm"
include "df-pjh.mm"
include "fnmpti.mm"

theorem pjmfn
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- projh Fn CH

  proof
    vh
    cch
    vx
    chil
    vx
    cv
    vz
    cv
    vy
    cv
    cva
    co
    wceq
    vy
    vh
    cv
    #
    cort
    cfv
    wrex
    vz
    @0
    crio
    #
    cmpt
    cpjh
    vx
    chil
    @1
    ax-hilex
    mptex
    vx
    vy
    vz
    vh
    df-pjh
    fnmpti
end

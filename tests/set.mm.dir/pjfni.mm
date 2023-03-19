include "chil.mm"
include "cv.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "cort.mm"
include "cfv.mm"
include "wrex.mm"
include "crio.mm"
include "cpjh.mm"
include "riotaex.mm"
include "cch.mm"
include "wcel.mm"
include "cmpt.mm"
include "pjhfval.mm"
include "ax-mp.mm"
include "fnmpti.mm"

theorem pjfni
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume pjfn.1: |- H e. CH


  assert |- ( projh ` H ) Fn ~H

  proof
    vx
    chil
    vx
    cv
    vy
    cv
    vz
    cv
    cva
    co
    wceq
    vz
    cH
    cort
    cfv
    wrex
    #
    vy
    cH
    crio
    #
    cH
    cpjh
    cfv
    #
    @0
    vy
    cH
    riotaex
    cH
    cch
    wcel
    @2
    vx
    chil
    @1
    cmpt
    wceq
    pjfn.1
    vx
    vz
    vy
    cH
    pjhfval
    ax-mp
    fnmpti
end

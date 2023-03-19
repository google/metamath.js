include "cnr.mm"
include "wcel.mm"
include "wa.mm"
include "cplr.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cpp.mm"
include "cer.mm"
include "cnp.mm"
include "df-nr.mm"
include "addsrpr.mm"
include "addcompr.mm"
include "ecovcom.mm"
include "dmaddsr.mm"
include "ndmovcom.mm"
include "pm2.61i.mm"

theorem addcomsr
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C


  assert |- ( A +R B ) = ( B +R A )

  proof
    cA
    cnr
    wcel
    cB
    cnr
    wcel
    wa
    cA
    cB
    cplr
    co
    cB
    cA
    cplr
    co
    wceq
    vx
    vy
    vz
    vw
    cA
    cB
    cnr
    vx
    cv
    #
    vz
    cv
    #
    cpp
    co
    cplr
    cer
    cnp
    vy
    cv
    #
    vw
    cv
    #
    cpp
    co
    @1
    @0
    cpp
    co
    @3
    @2
    cpp
    co
    df-nr
    @0
    @2
    @1
    @3
    addsrpr
    @1
    @3
    @0
    @2
    addsrpr
    @0
    @1
    addcompr
    @2
    @3
    addcompr
    ecovcom
    cA
    cB
    cnr
    cplr
    dmaddsr
    ndmovcom
    pm2.61i
end

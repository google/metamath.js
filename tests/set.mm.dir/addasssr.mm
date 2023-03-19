include "cnr.mm"
include "wcel.mm"
include "w3a.mm"
include "cplr.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cpp.mm"
include "cer.mm"
include "cnp.mm"
include "df-nr.mm"
include "addsrpr.mm"
include "wa.mm"
include "addclpr.mm"
include "anim12i.mm"
include "an4s.mm"
include "addasspr.mm"
include "ecovass.mm"
include "dmaddsr.mm"
include "0nsr.mm"
include "ndmovass.mm"
include "pm2.61i.mm"

theorem addasssr
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A +R B ) +R C ) = ( A +R ( B +R C ) )

  proof
    cA
    cnr
    wcel
    cB
    cnr
    wcel
    cC
    cnr
    wcel
    w3a
    cA
    cB
    cplr
    co
    cC
    cplr
    co
    cA
    cB
    cC
    cplr
    co
    cplr
    co
    wceq
    vx
    vy
    vz
    vw
    vv
    vu
    cA
    cB
    cC
    cnr
    cplr
    vw
    cv
    #
    vu
    cv
    #
    cpp
    co
    #
    cer
    cnp
    vx
    cv
    #
    vz
    cv
    #
    cpp
    co
    #
    vy
    cv
    #
    @0
    cpp
    co
    #
    @5
    vv
    cv
    #
    cpp
    co
    @7
    @1
    cpp
    co
    @3
    @4
    @8
    cpp
    co
    #
    cpp
    co
    @6
    @2
    cpp
    co
    @9
    df-nr
    @3
    @6
    @4
    @0
    addsrpr
    @4
    @0
    @8
    @1
    addsrpr
    @5
    @7
    @8
    @1
    addsrpr
    @3
    @6
    @9
    @2
    addsrpr
    @3
    cnp
    wcel
    #
    @4
    cnp
    wcel
    #
    @6
    cnp
    wcel
    #
    @0
    cnp
    wcel
    #
    @5
    cnp
    wcel
    #
    @7
    cnp
    wcel
    #
    wa
    @10
    @11
    wa
    @14
    @12
    @13
    wa
    @15
    @3
    @4
    addclpr
    @6
    @0
    addclpr
    anim12i
    an4s
    @11
    @8
    cnp
    wcel
    #
    @13
    @1
    cnp
    wcel
    #
    @9
    cnp
    wcel
    #
    @2
    cnp
    wcel
    #
    wa
    @11
    @16
    wa
    @18
    @13
    @17
    wa
    @19
    @4
    @8
    addclpr
    @0
    @1
    addclpr
    anim12i
    an4s
    @3
    @4
    @8
    addasspr
    @6
    @0
    @1
    addasspr
    ecovass
    cA
    cB
    cC
    cnr
    cplr
    dmaddsr
    0nsr
    ndmovass
    pm2.61i
end

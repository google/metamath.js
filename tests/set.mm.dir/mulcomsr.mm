include "cnr.mm"
include "wcel.mm"
include "wa.mm"
include "cmr.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cmp.mm"
include "cpp.mm"
include "cer.mm"
include "cnp.mm"
include "df-nr.mm"
include "mulsrpr.mm"
include "mulcompr.mm"
include "oveq12i.mm"
include "addcompr.mm"
include "eqtri.mm"
include "ecovcom.mm"
include "dmmulsr.mm"
include "ndmovcom.mm"
include "pm2.61i.mm"

theorem mulcomsr
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


  assert |- ( A .R B ) = ( B .R A )

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
    cmr
    co
    cB
    cA
    cmr
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
    cmp
    co
    #
    vy
    cv
    #
    vw
    cv
    #
    cmp
    co
    #
    cpp
    co
    cmr
    cer
    cnp
    @0
    @4
    cmp
    co
    #
    @3
    @1
    cmp
    co
    #
    cpp
    co
    #
    @1
    @0
    cmp
    co
    #
    @4
    @3
    cmp
    co
    #
    cpp
    co
    @1
    @3
    cmp
    co
    #
    @4
    @0
    cmp
    co
    #
    cpp
    co
    #
    df-nr
    @0
    @3
    @1
    @4
    mulsrpr
    @1
    @4
    @0
    @3
    mulsrpr
    @2
    @9
    @5
    @10
    cpp
    @0
    @1
    mulcompr
    @3
    @4
    mulcompr
    oveq12i
    @8
    @12
    @11
    cpp
    co
    @13
    @6
    @12
    @7
    @11
    cpp
    @0
    @4
    mulcompr
    @3
    @1
    mulcompr
    oveq12i
    @12
    @11
    addcompr
    eqtri
    ecovcom
    cA
    cB
    cnr
    cmr
    dmmulsr
    ndmovcom
    pm2.61i
end

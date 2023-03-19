include "cv.mm"
include "cablo.mm"
include "wcel.mm"
include "cc.mm"
include "crn.mm"
include "cxp.mm"
include "wf.mm"
include "c1.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "caddc.mm"
include "cmul.mm"
include "wa.mm"
include "w3a.mm"
include "cvc.mm"
include "df-vc.mm"
include "relopabi.mm"

theorem vcrel
  let vg: setvar g
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- Rel CVecOLD

  proof
    vg
    cv
    #
    cablo
    wcel
    cc
    @0
    crn
    #
    cxp
    @1
    vs
    cv
    #
    wf
    c1
    vx
    cv
    #
    @2
    co
    @3
    wceq
    vy
    cv
    #
    @3
    vz
    cv
    #
    @0
    co
    @2
    co
    @4
    @3
    @2
    co
    #
    @4
    @5
    @2
    co
    @0
    co
    wceq
    vz
    @1
    wral
    @4
    @5
    caddc
    co
    @3
    @2
    co
    @6
    @5
    @3
    @2
    co
    #
    @0
    co
    wceq
    @4
    @5
    cmul
    co
    @3
    @2
    co
    @4
    @7
    @2
    co
    wceq
    wa
    vz
    cc
    wral
    wa
    vy
    cc
    wral
    wa
    vx
    @1
    wral
    w3a
    vg
    vs
    cvc
    vx
    vy
    vz
    vg
    vs
    df-vc
    relopabi
end

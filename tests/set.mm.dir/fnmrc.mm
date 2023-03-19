include "cv.mm"
include "cuni.mm"
include "cpw.mm"
include "wss.mm"
include "crab.mm"
include "cint.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "cmrc.mm"
include "cmre.mm"
include "crn.mm"
include "wfn.mm"
include "df-mrc.mm"
include "fnmpt.mm"
include "cfv.mm"
include "mreunirn.mm"
include "cxp.mm"
include "wf.mm"
include "mrcflem.mm"
include "fssxp.mm"
include "syl.mm"
include "vuniex.mm"
include "pwex.mm"
include "vex.mm"
include "xpex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "sylbi.mm"
include "mprg.mm"

theorem fnmrc
  let cF: class F
  let vc: setvar c
  let vx: setvar x
  let vs: setvar s
  let cC: class C
  let cX: class X
  let cU: class U
  let cV: class V


  assert |- mrCls Fn U. ran Moore

  proof
    vx
    vc
    cv
    #
    cuni
    #
    cpw
    #
    vx
    cv
    vs
    cv
    wss
    vs
    @0
    crab
    cint
    cmpt
    #
    cvv
    wcel
    #
    cmrc
    cmre
    crn
    cuni
    #
    wfn
    vc
    @5
    vc
    @5
    @3
    cmrc
    cvv
    vx
    vs
    vc
    df-mrc
    fnmpt
    @0
    @5
    wcel
    @0
    @1
    cmre
    cfv
    wcel
    #
    @4
    @0
    mreunirn
    @6
    @3
    @2
    @0
    cxp
    #
    wss
    #
    @7
    cvv
    wcel
    @4
    @6
    @2
    @0
    @3
    wf
    @8
    vx
    @0
    @1
    vs
    mrcflem
    @2
    @0
    @3
    fssxp
    syl
    @2
    @0
    @1
    vc
    vuniex
    pwex
    vc
    vex
    xpex
    @3
    @7
    cvv
    ssexg
    sylancl
    sylbi
    mprg
end

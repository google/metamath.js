include "ccphlo.mm"
include "cnv.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "c1.mm"
include "cneg.mm"
include "caddc.mm"
include "cmul.mm"
include "wceq.mm"
include "crn.mm"
include "wral.mm"
include "coprab.mm"
include "cin.mm"
include "df-ph.mm"
include "inss1.mm"
include "eqsstri.mm"
include "sseli.mm"

theorem phnv
  let cU: class U
  let vg: setvar g
  let vn: setvar n
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y


  assert |- ( U e. CPreHilOLD -> U e. NrmCVec )

  proof
    ccphlo
    cnv
    cU
    ccphlo
    cnv
    vx
    cv
    #
    vy
    cv
    #
    vg
    cv
    #
    co
    vn
    cv
    #
    cfv
    c2
    cexp
    co
    @0
    c1
    cneg
    @1
    vs
    cv
    co
    @2
    co
    @3
    cfv
    c2
    cexp
    co
    caddc
    co
    c2
    @0
    @3
    cfv
    c2
    cexp
    co
    @1
    @3
    cfv
    c2
    cexp
    co
    caddc
    co
    cmul
    co
    wceq
    vy
    @2
    crn
    #
    wral
    vx
    @4
    wral
    vg
    vs
    vn
    coprab
    #
    cin
    cnv
    vx
    vy
    vg
    vn
    vs
    df-ph
    cnv
    @5
    inss1
    eqsstri
    sseli
end

include "cplr.mm"
include "cdm.mm"
include "cnr.mm"
include "cxp.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cer.mm"
include "cec.mm"
include "wceq.mm"
include "cpp.mm"
include "co.mm"
include "wex.mm"
include "coprab.mm"
include "df-plr.mm"
include "dmeqi.mm"
include "dmoprabss.mm"
include "eqsstri.mm"
include "0nsr.mm"
include "addclsr.mm"
include "oprssdm.mm"
include "eqssi.mm"

theorem dmaddsr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f


  assert |- dom +R = ( R. X. R. )

  proof
    cplr
    cdm
    #
    cnr
    cnr
    cxp
    #
    @0
    vx
    cv
    #
    cnr
    wcel
    vy
    cv
    #
    cnr
    wcel
    wa
    @2
    vw
    cv
    #
    vv
    cv
    #
    cop
    cer
    cec
    wceq
    @3
    vu
    cv
    #
    vf
    cv
    #
    cop
    cer
    cec
    wceq
    wa
    vz
    cv
    @4
    @6
    cpp
    co
    @5
    @7
    cpp
    co
    cop
    cer
    cec
    wceq
    wa
    vf
    wex
    vu
    wex
    vv
    wex
    vw
    wex
    #
    wa
    vx
    vy
    vz
    coprab
    #
    cdm
    @1
    cplr
    @9
    vx
    vy
    vz
    vw
    vv
    vu
    vf
    df-plr
    dmeqi
    @8
    vx
    vy
    vz
    cnr
    cnr
    dmoprabss
    eqsstri
    vx
    vy
    cnr
    cplr
    0nsr
    @2
    @3
    addclsr
    oprssdm
    eqssi
end

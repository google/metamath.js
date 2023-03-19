include "csubmnd.mm"
include "cfv.mm"
include "wcel.mm"
include "cdm.mm"
include "cmnd.mm"
include "cv.mm"
include "c0g.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "cbs.mm"
include "cpw.mm"
include "crab.mm"
include "df-submnd.mm"
include "dmmptss.mm"
include "elfvdm.mm"
include "sseldi.mm"

theorem submrcl
  let cS: class S
  let cM: class M
  let vm: setvar m
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vs: setvar s


  assert |- ( S e. ( SubMnd ` M ) -> M e. Mnd )

  proof
    cS
    cM
    csubmnd
    cfv
    wcel
    csubmnd
    cdm
    cmnd
    cM
    vs
    cmnd
    vs
    cv
    #
    c0g
    cfv
    vt
    cv
    #
    wcel
    vx
    cv
    vy
    cv
    @0
    cplusg
    cfv
    co
    @1
    wcel
    vy
    @1
    wral
    vx
    @1
    wral
    wa
    vt
    @0
    cbs
    cfv
    cpw
    crab
    csubmnd
    vx
    vy
    vt
    vs
    df-submnd
    dmmptss
    cS
    cM
    csubmnd
    elfvdm
    sseldi
end

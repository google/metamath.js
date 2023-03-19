include "csubmgm.mm"
include "cfv.mm"
include "wcel.mm"
include "cdm.mm"
include "cmgm.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "cbs.mm"
include "cpw.mm"
include "crab.mm"
include "df-submgm.mm"
include "dmmptss.mm"
include "elfvdm.mm"
include "sseldi.mm"

theorem submgmrcl
  let cS: class S
  let cM: class M
  let vs: setvar s
  let vt: setvar t
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k


  assert |- ( S e. ( SubMgm ` M ) -> M e. Mgm )

  proof
    cS
    cM
    csubmgm
    cfv
    wcel
    csubmgm
    cdm
    cmgm
    cM
    vs
    cmgm
    vx
    cv
    vy
    cv
    vs
    cv
    #
    cplusg
    cfv
    co
    vt
    cv
    #
    wcel
    vy
    @1
    wral
    vx
    @1
    wral
    vt
    @0
    cbs
    cfv
    cpw
    crab
    csubmgm
    vx
    vy
    vt
    vs
    df-submgm
    dmmptss
    cS
    cM
    csubmgm
    elfvdm
    sseldi
end

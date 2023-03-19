include "cmgm.mm"
include "wcel.mm"
include "cplusg.mm"
include "cfv.mm"
include "cbs.mm"
include "ccllaw.mm"
include "wbr.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "eqid.mm"
include "mgmcl.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "cvv.mm"
include "wa.mm"
include "wb.mm"
include "fvex.mm"
include "pm3.2i.mm"
include "iscllaw.mm"
include "mp1i.mm"
include "mpbird.mm"

theorem mgmplusgiopALT
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k


  assert |- ( M e. Mgm -> ( +g ` M ) clLaw ( Base ` M ) )

  proof
    cM
    cmgm
    wcel
    #
    cM
    cplusg
    cfv
    #
    cM
    cbs
    cfv
    #
    ccllaw
    wbr
    #
    vx
    cv
    #
    vy
    cv
    #
    @1
    co
    @2
    wcel
    #
    vy
    @2
    wral
    vx
    @2
    wral
    #
    @0
    @6
    vx
    vy
    @2
    @2
    @0
    @4
    @2
    wcel
    @5
    @2
    wcel
    @6
    @2
    cM
    @4
    @5
    @1
    @2
    eqid
    @1
    eqid
    mgmcl
    3expb
    ralrimivva
    @1
    cvv
    wcel
    #
    @2
    cvv
    wcel
    #
    wa
    @3
    @7
    wb
    @0
    @8
    @9
    cM
    cplusg
    fvex
    cM
    cbs
    fvex
    pm3.2i
    vx
    vy
    @2
    cvv
    cvv
    @1
    iscllaw
    mp1i
    mpbird
end

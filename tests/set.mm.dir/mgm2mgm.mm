include "cmgm2.mm"
include "wcel.mm"
include "cmgm.mm"
include "cplusg.mm"
include "cfv.mm"
include "cbs.mm"
include "ccllaw.mm"
include "wbr.mm"
include "eqid.mm"
include "ismgmALT.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "iscllaw.mm"
include "mp2an.mm"
include "ismgm.mm"
include "biimprd.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "pm2.43i.mm"
include "mgmplusgiopALT.mm"
include "mpbird.mm"
include "impbii.mm"

theorem mgm2mgm
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k


  assert |- ( M e. MgmALT <-> M e. Mgm )

  proof
    cM
    cmgm2
    wcel
    #
    cM
    cmgm
    wcel
    #
    @0
    @1
    @0
    @0
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
    @1
    @3
    cM
    cmgm2
    @2
    @3
    eqid
    #
    @2
    eqid
    #
    ismgmALT
    @4
    vx
    cv
    vy
    cv
    @2
    co
    @3
    wcel
    vy
    @3
    wral
    vx
    @3
    wral
    #
    @0
    @1
    @2
    cvv
    wcel
    @3
    cvv
    wcel
    @4
    @7
    wb
    cM
    cplusg
    fvex
    cM
    cbs
    fvex
    vx
    vy
    @3
    cvv
    cvv
    @2
    iscllaw
    mp2an
    @0
    @1
    @7
    vx
    vy
    @3
    cM
    cmgm2
    @2
    @5
    @6
    ismgm
    biimprd
    syl5bi
    sylbid
    pm2.43i
    @1
    @0
    @4
    cM
    mgmplusgiopALT
    @3
    cM
    cmgm
    @2
    @5
    @6
    ismgmALT
    mpbird
    impbii
end

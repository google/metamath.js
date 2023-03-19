include "comnd.mm"
include "wcel.mm"
include "cmnd.mm"
include "ctos.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "cplusg.mm"
include "co.mm"
include "wi.mm"
include "cbs.mm"
include "wral.mm"
include "eqid.mm"
include "isomnd.mm"
include "simp2bi.mm"

theorem omndtos
  let cM: class M
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- ( M e. oMnd -> M e. Toset )

  proof
    cM
    comnd
    wcel
    cM
    cmnd
    wcel
    cM
    ctos
    wcel
    va
    cv
    #
    vb
    cv
    #
    cM
    cple
    cfv
    #
    wbr
    @0
    vc
    cv
    #
    cM
    cplusg
    cfv
    #
    co
    @1
    @3
    @4
    co
    @2
    wbr
    wi
    vc
    cM
    cbs
    cfv
    #
    wral
    vb
    @5
    wral
    va
    @5
    wral
    @5
    @4
    @2
    cM
    va
    vb
    vc
    @5
    eqid
    @4
    eqid
    @2
    eqid
    isomnd
    simp2bi
end

include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cmgm.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "rzal.mm"
include "adantl.mm"
include "wb.mm"
include "eqid.mm"
include "ismgm.mm"
include "adantr.mm"
include "mpbird.mm"

theorem mgm0
  let cM: class M
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( M e. V /\ ( Base ` M ) = (/) ) -> M e. Mgm )

  proof
    cM
    cV
    wcel
    #
    cM
    cbs
    cfv
    #
    c0
    wceq
    #
    wa
    cM
    cmgm
    wcel
    #
    vx
    cv
    vy
    cv
    cM
    cplusg
    cfv
    #
    co
    @1
    wcel
    vy
    @1
    wral
    #
    vx
    @1
    wral
    #
    @2
    @6
    @0
    @5
    vx
    @1
    rzal
    adantl
    @0
    @3
    @6
    wb
    @2
    vx
    vy
    @1
    cM
    cV
    @4
    @1
    eqid
    @4
    eqid
    ismgm
    adantr
    mpbird
end

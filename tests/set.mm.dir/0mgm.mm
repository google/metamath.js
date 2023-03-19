include "wcel.mm"
include "cmgm.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "c0.mm"
include "wral.mm"
include "ral0.mm"
include "cbs.mm"
include "eqcomi.mm"
include "eqid.mm"
include "ismgm.mm"
include "mpbiri.mm"

theorem 0mgm
  let cM: class M
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume 0mgm.b: |- ( Base ` M ) = (/)


  assert |- ( M e. V -> M e. Mgm )

  proof
    cM
    cV
    wcel
    cM
    cmgm
    wcel
    vx
    cv
    vy
    cv
    cM
    cplusg
    cfv
    #
    co
    c0
    wcel
    vy
    c0
    wral
    #
    vx
    c0
    wral
    @1
    vx
    ral0
    vx
    vy
    c0
    cM
    cV
    @0
    cM
    cbs
    cfv
    c0
    0mgm.b
    eqcomi
    @0
    eqid
    ismgm
    mpbiri
end

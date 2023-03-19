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
include "csgrp.mm"
include "mgm0.mm"
include "rzal.mm"
include "adantl.mm"
include "eqid.mm"
include "issgrp.mm"
include "sylanbrc.mm"

theorem sgrp0
  let cM: class M
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( M e. V /\ ( Base ` M ) = (/) ) -> M e. SGrp )

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
    vx
    cv
    #
    vy
    cv
    #
    cM
    cplusg
    cfv
    #
    co
    vz
    cv
    #
    @5
    co
    @3
    @4
    @6
    @5
    co
    @5
    co
    wceq
    vz
    @1
    wral
    vy
    @1
    wral
    #
    vx
    @1
    wral
    #
    cM
    csgrp
    wcel
    cM
    cV
    mgm0
    @2
    @8
    @0
    @7
    vx
    @1
    rzal
    adantl
    vx
    vy
    vz
    @1
    cM
    @5
    @1
    eqid
    @5
    eqid
    issgrp
    sylanbrc
end

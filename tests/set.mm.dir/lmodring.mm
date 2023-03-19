include "clmod.mm"
include "wcel.mm"
include "cgrp.mm"
include "crg.mm"
include "cv.mm"
include "cvsca.mm"
include "cfv.mm"
include "co.mm"
include "cbs.mm"
include "cplusg.mm"
include "wceq.mm"
include "w3a.mm"
include "cmulr.mm"
include "cur.mm"
include "wa.mm"
include "wral.mm"
include "eqid.mm"
include "islmod.mm"
include "simp2bi.mm"

theorem lmodring
  let cF: class F
  let cW: class W
  let vq: setvar q
  let vr: setvar r
  let vw: setvar w
  let vx: setvar x
  assume lmodring.1: |- F = ( Scalar ` W )


  assert |- ( W e. LMod -> F e. Ring )

  proof
    cW
    clmod
    wcel
    cW
    cgrp
    wcel
    cF
    crg
    wcel
    vr
    cv
    #
    vw
    cv
    #
    cW
    cvsca
    cfv
    #
    co
    #
    cW
    cbs
    cfv
    #
    wcel
    @0
    @1
    vx
    cv
    #
    cW
    cplusg
    cfv
    #
    co
    @2
    co
    @3
    @0
    @5
    @2
    co
    @6
    co
    wceq
    vq
    cv
    #
    @0
    cF
    cplusg
    cfv
    #
    co
    @1
    @2
    co
    @7
    @1
    @2
    co
    @3
    @6
    co
    wceq
    w3a
    @7
    @0
    cF
    cmulr
    cfv
    #
    co
    @1
    @2
    co
    @7
    @3
    @2
    co
    wceq
    cF
    cur
    cfv
    #
    @1
    @2
    co
    @1
    wceq
    wa
    wa
    vw
    @4
    wral
    vx
    @4
    wral
    vr
    cF
    cbs
    cfv
    #
    wral
    vq
    @11
    wral
    vx
    vw
    @6
    @8
    @2
    @9
    @10
    cF
    @11
    @4
    cW
    vr
    vq
    @4
    eqid
    @6
    eqid
    @2
    eqid
    lmodring.1
    @11
    eqid
    @8
    eqid
    @9
    eqid
    @10
    eqid
    islmod
    simp2bi
end

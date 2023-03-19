include "clmod.mm"
include "wcel.mm"
include "cgrp.mm"
include "csca.mm"
include "cfv.mm"
include "crg.mm"
include "cv.mm"
include "cvsca.mm"
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
include "simp1bi.mm"

theorem lmodgrp
  let cW: class W
  let vq: setvar q
  let vr: setvar r
  let vw: setvar w
  let vx: setvar x
  let cF: class F


  assert |- ( W e. LMod -> W e. Grp )

  proof
    cW
    clmod
    wcel
    cW
    cgrp
    wcel
    cW
    csca
    cfv
    #
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
    @1
    @2
    vx
    cv
    #
    cW
    cplusg
    cfv
    #
    co
    @3
    co
    @4
    @1
    @6
    @3
    co
    @7
    co
    wceq
    vq
    cv
    #
    @1
    @0
    cplusg
    cfv
    #
    co
    @2
    @3
    co
    @8
    @2
    @3
    co
    @4
    @7
    co
    wceq
    w3a
    @8
    @1
    @0
    cmulr
    cfv
    #
    co
    @2
    @3
    co
    @8
    @4
    @3
    co
    wceq
    @0
    cur
    cfv
    #
    @2
    @3
    co
    @2
    wceq
    wa
    wa
    vw
    @5
    wral
    vx
    @5
    wral
    vr
    @0
    cbs
    cfv
    #
    wral
    vq
    @12
    wral
    vx
    vw
    @7
    @9
    @3
    @10
    @11
    @0
    @12
    @5
    cW
    vr
    vq
    @5
    eqid
    @7
    eqid
    @3
    eqid
    @0
    eqid
    @12
    eqid
    @9
    eqid
    @10
    eqid
    @11
    eqid
    islmod
    simp1bi
end

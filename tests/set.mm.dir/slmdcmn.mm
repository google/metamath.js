include "cslmd.mm"
include "wcel.mm"
include "ccmn.mm"
include "csca.mm"
include "cfv.mm"
include "csrg.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "cbs.mm"
include "cplusg.mm"
include "wceq.mm"
include "w3a.mm"
include "cmulr.mm"
include "cur.mm"
include "c0g.mm"
include "wa.mm"
include "wral.mm"
include "eqid.mm"
include "isslmd.mm"
include "simp1bi.mm"

theorem slmdcmn
  let cW: class W
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F


  assert |- ( W e. SLMod -> W e. CMnd )

  proof
    cW
    cslmd
    wcel
    cW
    ccmn
    wcel
    cW
    csca
    cfv
    #
    csrg
    wcel
    vz
    cv
    #
    vy
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
    vw
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
    @0
    c0g
    cfv
    #
    @2
    @3
    co
    cW
    c0g
    cfv
    #
    wceq
    w3a
    wa
    vy
    @5
    wral
    vx
    @5
    wral
    vz
    @0
    cbs
    cfv
    #
    wral
    vw
    @14
    wral
    vx
    vy
    @7
    @9
    @3
    @10
    @11
    @0
    @14
    @12
    @5
    cW
    @13
    vz
    vw
    @5
    eqid
    @7
    eqid
    @3
    eqid
    @13
    eqid
    @0
    eqid
    @14
    eqid
    @9
    eqid
    @10
    eqid
    @11
    eqid
    @12
    eqid
    isslmd
    simp1bi
end

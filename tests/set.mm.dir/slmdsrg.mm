include "cslmd.mm"
include "wcel.mm"
include "ccmn.mm"
include "csrg.mm"
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
include "c0g.mm"
include "wa.mm"
include "wral.mm"
include "eqid.mm"
include "isslmd.mm"
include "simp2bi.mm"

theorem slmdsrg
  let cF: class F
  let cW: class W
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume slmdsrg.1: |- F = ( Scalar ` W )


  assert |- ( W e. SLMod -> F e. SRing )

  proof
    cW
    cslmd
    wcel
    cW
    ccmn
    wcel
    cF
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
    vw
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
    cF
    c0g
    cfv
    #
    @1
    @2
    co
    cW
    c0g
    cfv
    #
    wceq
    w3a
    wa
    vy
    @4
    wral
    vx
    @4
    wral
    vz
    cF
    cbs
    cfv
    #
    wral
    vw
    @13
    wral
    vx
    vy
    @6
    @8
    @2
    @9
    @10
    cF
    @13
    @11
    @4
    cW
    @12
    vz
    vw
    @4
    eqid
    @6
    eqid
    @2
    eqid
    @12
    eqid
    slmdsrg.1
    @13
    eqid
    @8
    eqid
    @9
    eqid
    @10
    eqid
    @11
    eqid
    isslmd
    simp2bi
end

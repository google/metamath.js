include "csrg.mm"
include "wcel.mm"
include "ccmn.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmnd.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "cmulr.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "wral.mm"
include "c0g.mm"
include "eqid.mm"
include "issrg.mm"
include "simp1bi.mm"

theorem srgcmn
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( R e. SRing -> R e. CMnd )

  proof
    cR
    csrg
    wcel
    cR
    ccmn
    wcel
    cR
    cmgp
    cfv
    #
    cmnd
    wcel
    vx
    cv
    #
    vy
    cv
    #
    vz
    cv
    #
    cR
    cplusg
    cfv
    #
    co
    cR
    cmulr
    cfv
    #
    co
    @1
    @2
    @5
    co
    @1
    @3
    @5
    co
    #
    @4
    co
    wceq
    @1
    @2
    @4
    co
    @3
    @5
    co
    @6
    @2
    @3
    @5
    co
    @4
    co
    wceq
    wa
    vz
    cR
    cbs
    cfv
    #
    wral
    vy
    @7
    wral
    cR
    c0g
    cfv
    #
    @1
    @5
    co
    @8
    wceq
    @1
    @8
    @5
    co
    @8
    wceq
    wa
    wa
    vx
    @7
    wral
    vx
    vy
    vz
    @7
    @4
    cR
    @5
    @0
    @8
    @7
    eqid
    @0
    eqid
    @4
    eqid
    @5
    eqid
    @8
    eqid
    issrg
    simp1bi
end

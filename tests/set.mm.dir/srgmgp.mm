include "csrg.mm"
include "wcel.mm"
include "ccmn.mm"
include "cmnd.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "cmulr.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "wral.mm"
include "c0g.mm"
include "eqid.mm"
include "issrg.mm"
include "simp2bi.mm"

theorem srgmgp
  let cR: class R
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume srgmgp.g: |- G = ( mulGrp ` R )


  assert |- ( R e. SRing -> G e. Mnd )

  proof
    cR
    csrg
    wcel
    cR
    ccmn
    wcel
    cG
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
    @0
    @1
    @4
    co
    @0
    @2
    @4
    co
    #
    @3
    co
    wceq
    @0
    @1
    @3
    co
    @2
    @4
    co
    @5
    @1
    @2
    @4
    co
    @3
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
    @6
    wral
    cR
    c0g
    cfv
    #
    @0
    @4
    co
    @7
    wceq
    @0
    @7
    @4
    co
    @7
    wceq
    wa
    wa
    vx
    @6
    wral
    vx
    vy
    vz
    @6
    @3
    cR
    @4
    cG
    @7
    @6
    eqid
    srgmgp.g
    @3
    eqid
    @4
    eqid
    @7
    eqid
    issrg
    simp2bi
end

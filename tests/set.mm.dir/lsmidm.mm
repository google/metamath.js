include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "co.mm"
include "cv.mm"
include "cplusg.mm"
include "cmpt2.mm"
include "crn.mm"
include "wceq.mm"
include "cbs.mm"
include "eqid.mm"
include "lsmval.mm"
include "anidms.mm"
include "cxp.mm"
include "wf.mm"
include "wss.mm"
include "wral.mm"
include "subgcl.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "fmpt2.mm"
include "sylib.mm"
include "frn.mm"
include "syl.mm"
include "eqsstrd.mm"
include "lsmub1.mm"
include "eqssd.mm"

theorem lsmidm
  let c.po: class .(+)
  let cU: class U
  let cG: class G
  let va: setvar a
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vb: setvar b
  let cR: class R
  let cT: class T
  assume lsmub1.p: |- .(+) = ( LSSum ` G )


  assert |- ( U e. ( SubGrp ` G ) -> ( U .(+) U ) = U )

  proof
    cU
    cG
    csubg
    cfv
    wcel
    #
    cU
    cU
    c.po
    co
    #
    cU
    @0
    @1
    vx
    vy
    cU
    cU
    vx
    cv
    #
    vy
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cmpt2
    #
    crn
    #
    cU
    @0
    @1
    @7
    wceq
    vx
    vy
    cG
    cbs
    cfv
    #
    @4
    c.po
    cU
    cU
    cG
    @8
    eqid
    @4
    eqid
    #
    lsmub1.p
    lsmval
    anidms
    @0
    cU
    cU
    cxp
    #
    cU
    @6
    wf
    #
    @7
    cU
    wss
    @0
    @5
    cU
    wcel
    #
    vy
    cU
    wral
    vx
    cU
    wral
    @11
    @0
    @12
    vx
    vy
    cU
    cU
    @0
    @2
    cU
    wcel
    @3
    cU
    wcel
    @12
    @4
    cU
    cG
    @2
    @3
    @9
    subgcl
    3expb
    ralrimivva
    vx
    vy
    cU
    cU
    @5
    cU
    @6
    @6
    eqid
    fmpt2
    sylib
    @10
    cU
    @6
    frn
    syl
    eqsstrd
    @0
    cU
    @1
    wss
    c.po
    cU
    cU
    cG
    lsmub1.p
    lsmub1
    anidms
    eqssd
end

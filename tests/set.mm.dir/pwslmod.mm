include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "csca.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cprds.mm"
include "co.mm"
include "eqid.mm"
include "pwsval.mm"
include "crg.mm"
include "lmodring.mm"
include "adantr.mm"
include "simpr.mm"
include "wf.mm"
include "fconst6g.mm"
include "cv.mm"
include "wceq.mm"
include "fvconst2g.mm"
include "adantlr.mm"
include "fveq2d.mm"
include "prdslmodd.mm"
include "eqeltrd.mm"

theorem pwslmod
  let cR: class R
  let cI: class I
  let cV: class V
  let cY: class Y
  let vx: setvar x
  assume pwslmod.y: |- Y = ( R ^s I )


  assert |- ( ( R e. LMod /\ I e. V ) -> Y e. LMod )

  proof
    cR
    clmod
    wcel
    #
    cI
    cV
    wcel
    #
    wa
    #
    cY
    cR
    csca
    cfv
    #
    cI
    cR
    csn
    cxp
    #
    cprds
    co
    #
    clmod
    cR
    @3
    cI
    clmod
    cV
    cY
    pwslmod.y
    @3
    eqid
    #
    pwsval
    @2
    vx
    @4
    @3
    cI
    cV
    @5
    @5
    eqid
    @0
    @3
    crg
    wcel
    @1
    @3
    cR
    @6
    lmodring
    adantr
    @0
    @1
    simpr
    @0
    cI
    clmod
    @4
    wf
    @1
    cI
    cR
    clmod
    fconst6g
    adantr
    @2
    vx
    cv
    #
    cI
    wcel
    #
    wa
    @7
    @4
    cfv
    #
    cR
    csca
    @0
    @8
    @9
    cR
    wceq
    @1
    cI
    cR
    @7
    clmod
    fvconst2g
    adantlr
    fveq2d
    prdslmodd
    eqeltrd
end

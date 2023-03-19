include "ccmn.mm"
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
include "cvv.mm"
include "simpr.mm"
include "fvexd.mm"
include "wf.mm"
include "fconst6g.mm"
include "adantr.mm"
include "prdscmnd.mm"
include "eqeltrd.mm"

theorem pwscmn
  let cR: class R
  let cI: class I
  let cV: class V
  let cY: class Y
  assume pwscmn.y: |- Y = ( R ^s I )


  assert |- ( ( R e. CMnd /\ I e. V ) -> Y e. CMnd )

  proof
    cR
    ccmn
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
    ccmn
    cR
    @3
    cI
    ccmn
    cV
    cY
    pwscmn.y
    @3
    eqid
    pwsval
    @2
    @4
    @3
    cI
    cvv
    cV
    @5
    @5
    eqid
    @0
    @1
    simpr
    @2
    cR
    csca
    fvexd
    @0
    cI
    ccmn
    @4
    wf
    @1
    cI
    cR
    ccmn
    fconst6g
    adantr
    prdscmnd
    eqeltrd
end

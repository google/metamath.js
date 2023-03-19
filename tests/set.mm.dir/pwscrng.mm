include "ccrg.mm"
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
include "prdscrngd.mm"
include "eqeltrd.mm"

theorem pwscrng
  let cR: class R
  let cI: class I
  let cV: class V
  let cY: class Y
  assume pwscrng.y: |- Y = ( R ^s I )


  assert |- ( ( R e. CRing /\ I e. V ) -> Y e. CRing )

  proof
    cR
    ccrg
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
    ccrg
    cR
    @3
    cI
    ccrg
    cV
    cY
    pwscrng.y
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
    ccrg
    @4
    wf
    @1
    cI
    cR
    ccrg
    fconst6g
    adantr
    prdscrngd
    eqeltrd
end

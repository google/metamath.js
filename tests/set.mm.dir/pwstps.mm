include "ctps.mm"
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
include "fvexd.mm"
include "simpr.mm"
include "wf.mm"
include "fconst6g.mm"
include "adantr.mm"
include "prdstps.mm"
include "eqeltrd.mm"

theorem pwstps
  let cR: class R
  let cI: class I
  let cV: class V
  let cY: class Y
  assume pwstps.y: |- Y = ( R ^s I )


  assert |- ( ( R e. TopSp /\ I e. V ) -> Y e. TopSp )

  proof
    cR
    ctps
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
    ctps
    cR
    @3
    cI
    ctps
    cV
    cY
    pwstps.y
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
    @2
    cR
    csca
    fvexd
    @0
    @1
    simpr
    @0
    cI
    ctps
    @4
    wf
    @1
    cI
    cR
    ctps
    fconst6g
    adantr
    prdstps
    eqeltrd
end

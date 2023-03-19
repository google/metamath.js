include "cxme.mm"
include "wcel.mm"
include "cfn.mm"
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
include "wf.mm"
include "fvexd.mm"
include "simpr.mm"
include "fconst6g.mm"
include "adantr.mm"
include "prdsxms.mm"
include "syl3anc.mm"
include "eqeltrd.mm"

theorem pwsxms
  let cR: class R
  let cI: class I
  let cY: class Y
  assume pwsms.y: |- Y = ( R ^s I )


  assert |- ( ( R e. *MetSp /\ I e. Fin ) -> Y e. *MetSp )

  proof
    cR
    cxme
    wcel
    #
    cI
    cfn
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
    cxme
    cR
    @3
    cI
    cxme
    cfn
    cY
    pwsms.y
    @3
    eqid
    pwsval
    @2
    @3
    cvv
    wcel
    @1
    cI
    cxme
    @4
    wf
    #
    @5
    cxme
    wcel
    @2
    cR
    csca
    fvexd
    @0
    @1
    simpr
    @0
    @6
    @1
    cI
    cR
    cxme
    fconst6g
    adantr
    @4
    @3
    cI
    cvv
    @5
    @5
    eqid
    prdsxms
    syl3anc
    eqeltrd
end

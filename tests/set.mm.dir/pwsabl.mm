include "cabl.mm"
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
include "prdsabld.mm"
include "eqeltrd.mm"

theorem pwsabl
  let cR: class R
  let cI: class I
  let cV: class V
  let cY: class Y
  assume pwscmn.y: |- Y = ( R ^s I )


  assert |- ( ( R e. Abel /\ I e. V ) -> Y e. Abel )

  proof
    cR
    cabl
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
    cabl
    cR
    @3
    cI
    cabl
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
    cabl
    @4
    wf
    @1
    cI
    cR
    cabl
    fconst6g
    adantr
    prdsabld
    eqeltrd
end

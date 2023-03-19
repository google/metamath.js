include "cmnd.mm"
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
include "prdsmndd.mm"
include "eqeltrd.mm"

theorem pwsmnd
  let cR: class R
  let cI: class I
  let cV: class V
  let cY: class Y
  let vx: setvar x
  let vr: setvar r
  let c.0: class .0.
  assume pwsmnd.y: |- Y = ( R ^s I )


  assert |- ( ( R e. Mnd /\ I e. V ) -> Y e. Mnd )

  proof
    cR
    cmnd
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
    cmnd
    cR
    @3
    cI
    cmnd
    cV
    cY
    pwsmnd.y
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
    cmnd
    @4
    wf
    @1
    cI
    cR
    cmnd
    fconst6g
    adantr
    prdsmndd
    eqeltrd
end

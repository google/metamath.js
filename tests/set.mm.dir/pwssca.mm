include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "cprds.mm"
include "co.mm"
include "csca.mm"
include "cfv.mm"
include "cvv.mm"
include "eqid.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "simpr.mm"
include "snex.mm"
include "xpexg.mm"
include "sylancl.mm"
include "prdssca.mm"
include "pwsval.mm"
include "fveq2d.mm"
include "eqtr4d.mm"

theorem pwssca
  let cR: class R
  let cS: class S
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  assume pwssca.y: |- Y = ( R ^s I )
  assume pwssca.s: |- S = ( Scalar ` R )


  assert |- ( ( R e. V /\ I e. W ) -> S = ( Scalar ` Y ) )

  proof
    cR
    cV
    wcel
    #
    cI
    cW
    wcel
    #
    wa
    #
    cS
    cS
    cI
    cR
    csn
    #
    cxp
    #
    cprds
    co
    #
    csca
    cfv
    cY
    csca
    cfv
    @2
    @5
    @4
    cS
    cvv
    cvv
    @5
    eqid
    cS
    cvv
    wcel
    @2
    cS
    cR
    csca
    cfv
    cvv
    pwssca.s
    cR
    csca
    fvex
    eqeltri
    a1i
    @2
    @1
    @3
    cvv
    wcel
    @4
    cvv
    wcel
    @0
    @1
    simpr
    cR
    snex
    cI
    @3
    cW
    cvv
    xpexg
    sylancl
    prdssca
    @2
    cY
    @5
    csca
    cR
    cS
    cI
    cV
    cW
    cY
    pwssca.y
    pwssca.s
    pwsval
    fveq2d
    eqtr4d
end

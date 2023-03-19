include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "csca.mm"
include "csn.mm"
include "cxp.mm"
include "cprds.mm"
include "co.mm"
include "cixp.mm"
include "cmap.mm"
include "eqid.mm"
include "pwsval.mm"
include "fveq2d.mm"
include "cv.mm"
include "cvv.mm"
include "fvexd.mm"
include "simpr.mm"
include "snex.mm"
include "xpexg.mm"
include "sylancl.mm"
include "c0.mm"
include "wne.mm"
include "cdm.mm"
include "wceq.mm"
include "snnzg.mm"
include "adantr.mm"
include "dmxp.mm"
include "syl.mm"
include "prdsbas.mm"
include "wral.mm"
include "fvconst2g.mm"
include "ralrimiva.mm"
include "ixpeq2.mm"
include "eqtrd.mm"
include "fvex.mm"
include "ixpconstg.mm"
include "oveq1i.mm"
include "syl6eqr.mm"
include "3eqtrrd.mm"

theorem pwsbas
  let cB: class B
  let cR: class R
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let vx: setvar x
  assume pwsbas.y: |- Y = ( R ^s I )
  assume pwsbas.f: |- B = ( Base ` R )


  assert |- ( ( R e. V /\ I e. W ) -> ( B ^m I ) = ( Base ` Y ) )

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
    cY
    cbs
    cfv
    cR
    csca
    cfv
    #
    cI
    cR
    csn
    #
    cxp
    #
    cprds
    co
    #
    cbs
    cfv
    #
    vx
    cI
    cR
    cbs
    cfv
    #
    cixp
    #
    cB
    cI
    cmap
    co
    #
    @2
    cY
    @6
    cbs
    cR
    @3
    cI
    cV
    cW
    cY
    pwsbas.y
    @3
    eqid
    pwsval
    fveq2d
    @2
    @7
    vx
    cI
    vx
    cv
    #
    @5
    cfv
    #
    cbs
    cfv
    #
    cixp
    #
    @9
    @2
    vx
    @7
    @6
    @5
    @3
    cI
    cvv
    cvv
    @6
    eqid
    @2
    cR
    csca
    fvexd
    @2
    @1
    @4
    cvv
    wcel
    @5
    cvv
    wcel
    @0
    @1
    simpr
    #
    cR
    snex
    cI
    @4
    cW
    cvv
    xpexg
    sylancl
    @7
    eqid
    @2
    @4
    c0
    wne
    #
    @5
    cdm
    cI
    wceq
    @0
    @16
    @1
    cR
    cV
    snnzg
    adantr
    cI
    @4
    dmxp
    syl
    prdsbas
    @2
    @13
    @8
    wceq
    #
    vx
    cI
    wral
    #
    @14
    @9
    wceq
    @0
    @18
    @1
    @0
    @17
    vx
    cI
    @0
    @11
    cI
    wcel
    wa
    @12
    cR
    cbs
    cI
    cR
    @11
    cV
    fvconst2g
    fveq2d
    ralrimiva
    adantr
    vx
    cI
    @13
    @8
    ixpeq2
    syl
    eqtrd
    @2
    @9
    @8
    cI
    cmap
    co
    #
    @10
    @2
    @1
    @8
    cvv
    wcel
    @9
    @19
    wceq
    @15
    cR
    cbs
    fvex
    vx
    cI
    @8
    cW
    cvv
    ixpconstg
    sylancl
    cB
    @8
    cI
    cmap
    pwsbas.f
    oveq1i
    syl6eqr
    3eqtrrd
end

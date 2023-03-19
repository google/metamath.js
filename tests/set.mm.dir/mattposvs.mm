include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "csn.mm"
include "cmulr.mm"
include "cfv.mm"
include "cof.mm"
include "co.mm"
include "ctpos.mm"
include "wceq.mm"
include "cvv.mm"
include "cfn.mm"
include "matrcl.mm"
include "simpld.mm"
include "sqxpexg.mm"
include "syl.mm"
include "snex.mm"
include "xpexg.mm"
include "sylancl.mm"
include "oftpos.mm"
include "mpancom.mm"
include "tposconst.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "adantl.mm"
include "eqid.mm"
include "matvsca2.mm"
include "tposeqd.mm"
include "mattposcl.mm"
include "sylan2.mm"
include "3eqtr4d.mm"

theorem mattposvs
  let cA: class A
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cK: class K
  let cN: class N
  let cX: class X
  let cY: class Y
  assume mattposvs.a: |- A = ( N Mat R )
  assume mattposvs.b: |- B = ( Base ` A )
  assume mattposvs.k: |- K = ( Base ` R )
  assume mattposvs.v: |- .x. = ( .s ` A )


  assert |- ( ( X e. K /\ Y e. B ) -> tpos ( X .x. Y ) = ( X .x. tpos Y ) )

  proof
    cX
    cK
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cN
    cN
    cxp
    #
    cX
    csn
    #
    cxp
    #
    cY
    cR
    cmulr
    cfv
    #
    cof
    #
    co
    #
    ctpos
    #
    @5
    cY
    ctpos
    #
    @7
    co
    #
    cX
    cY
    c.x
    co
    #
    ctpos
    cX
    @10
    c.x
    co
    #
    @1
    @9
    @11
    wceq
    @0
    @1
    @9
    @5
    ctpos
    #
    @10
    @7
    co
    #
    @11
    @5
    cvv
    wcel
    #
    @1
    @9
    @15
    wceq
    @1
    @3
    cvv
    wcel
    #
    @4
    cvv
    wcel
    @16
    @1
    cN
    cfn
    wcel
    #
    @17
    @1
    @18
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cY
    mattposvs.a
    mattposvs.b
    matrcl
    simpld
    cN
    cfn
    sqxpexg
    syl
    cX
    snex
    @3
    @4
    cvv
    cvv
    xpexg
    sylancl
    @6
    @5
    cY
    cvv
    cB
    oftpos
    mpancom
    @14
    @5
    @10
    @7
    cN
    cN
    cX
    tposconst
    oveq1i
    syl6eq
    adantl
    @2
    @12
    @8
    cA
    cB
    @3
    cR
    c.x
    @6
    cK
    cN
    cX
    cY
    mattposvs.a
    mattposvs.b
    mattposvs.k
    mattposvs.v
    @6
    eqid
    #
    @3
    eqid
    #
    matvsca2
    tposeqd
    @1
    @0
    @10
    cB
    wcel
    @13
    @11
    wceq
    cA
    cB
    cR
    cY
    cN
    mattposvs.a
    mattposvs.b
    mattposcl
    cA
    cB
    @3
    cR
    c.x
    @6
    cK
    cN
    cX
    @10
    mattposvs.a
    mattposvs.b
    mattposvs.k
    mattposvs.v
    @19
    @20
    matvsca2
    sylan2
    3eqtr4d
end

include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "ctx.mm"
include "co.mm"
include "ctop.mm"
include "cxp.mm"
include "cuni.mm"
include "wceq.mm"
include "topontop.mm"
include "txtop.mm"
include "syl2an.mm"
include "cv.mm"
include "cmpt2.mm"
include "crn.mm"
include "ctg.mm"
include "eqid.mm"
include "txuni2.mm"
include "toponuni.mm"
include "xpeq12.mm"
include "cvv.mm"
include "txbasex.mm"
include "unitg.mm"
include "syl.mm"
include "3eqtr4a.mm"
include "txval.mm"
include "unieqd.mm"
include "eqtr4d.mm"
include "istopon.mm"
include "sylanbrc.mm"

theorem txtopon
  let cR: class R
  let cS: class S
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vv: setvar v


  assert |- ( ( R e. ( TopOn ` X ) /\ S e. ( TopOn ` Y ) ) -> ( R tX S ) e. ( TopOn ` ( X X. Y ) ) )

  proof
    cR
    cX
    ctopon
    cfv
    #
    wcel
    #
    cS
    cY
    ctopon
    cfv
    #
    wcel
    #
    wa
    #
    cR
    cS
    ctx
    co
    #
    ctop
    wcel
    #
    cX
    cY
    cxp
    #
    @5
    cuni
    #
    wceq
    @5
    @7
    ctopon
    cfv
    wcel
    @1
    cR
    ctop
    wcel
    cS
    ctop
    wcel
    @6
    @3
    cX
    cR
    topontop
    cY
    cS
    topontop
    cR
    cS
    txtop
    syl2an
    @4
    @7
    vu
    vv
    cR
    cS
    vu
    cv
    vv
    cv
    cxp
    cmpt2
    crn
    #
    ctg
    cfv
    #
    cuni
    #
    @8
    @4
    cR
    cuni
    #
    cS
    cuni
    #
    cxp
    #
    @9
    cuni
    #
    @7
    @11
    vu
    vv
    @9
    cR
    cS
    @12
    @13
    @9
    eqid
    #
    @12
    eqid
    @13
    eqid
    txuni2
    @1
    cX
    @12
    wceq
    cY
    @13
    wceq
    @7
    @14
    wceq
    @3
    cX
    cR
    toponuni
    cY
    cS
    toponuni
    cX
    @12
    cY
    @13
    xpeq12
    syl2an
    @4
    @9
    cvv
    wcel
    @11
    @15
    wceq
    vu
    vv
    @9
    cR
    cS
    @0
    @2
    @16
    txbasex
    @9
    cvv
    unitg
    syl
    3eqtr4a
    @4
    @5
    @10
    vu
    vv
    @9
    cR
    cS
    @0
    @2
    @16
    txval
    unieqd
    eqtr4d
    @7
    @5
    istopon
    sylanbrc
end

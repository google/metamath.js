include "wcel.mm"
include "cuss.mm"
include "cfv.mm"
include "cxp.mm"
include "crest.mm"
include "co.mm"
include "cunif.mm"
include "cbs.mm"
include "cin.mm"
include "cress.mm"
include "eqid.mm"
include "ussval.mm"
include "oveq1i.mm"
include "cvv.mm"
include "wceq.mm"
include "fvex.mm"
include "a1i.mm"
include "xpex.mm"
include "sqxpexg.mm"
include "restco.mm"
include "syl3anc.mm"
include "syl5eqr.mm"
include "inxp.mm"
include "incom.mm"
include "ressbas.mm"
include "sqxpeqd.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "ressunif.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "eqtr2d.mm"

theorem ressuss
  let cA: class A
  let cV: class V
  let cW: class W


  assert |- ( A e. V -> ( UnifSt ` ( W |`s A ) ) = ( ( UnifSt ` W ) |`t ( A X. A ) ) )

  proof
    cA
    cV
    wcel
    #
    cW
    cuss
    cfv
    #
    cA
    cA
    cxp
    #
    crest
    co
    #
    cW
    cunif
    cfv
    #
    cW
    cbs
    cfv
    #
    @5
    cxp
    #
    @2
    cin
    #
    crest
    co
    #
    cW
    cA
    cress
    co
    #
    cuss
    cfv
    #
    @0
    @3
    @4
    @6
    crest
    co
    #
    @2
    crest
    co
    #
    @8
    @11
    @1
    @2
    crest
    @5
    @4
    cW
    @5
    eqid
    #
    @4
    eqid
    #
    ussval
    oveq1i
    @0
    @4
    cvv
    wcel
    #
    @6
    cvv
    wcel
    #
    @2
    cvv
    wcel
    @12
    @8
    wceq
    @15
    @0
    cW
    cunif
    fvex
    a1i
    @16
    @0
    @5
    @5
    cW
    cbs
    fvex
    #
    @17
    xpex
    a1i
    cA
    cV
    sqxpexg
    @6
    @2
    @4
    cvv
    cvv
    cvv
    restco
    syl3anc
    syl5eqr
    @0
    @8
    @4
    @9
    cbs
    cfv
    #
    @18
    cxp
    #
    crest
    co
    @9
    cunif
    cfv
    #
    @19
    crest
    co
    #
    @10
    @0
    @7
    @19
    @4
    crest
    @0
    @7
    @5
    cA
    cin
    #
    @22
    cxp
    @19
    @5
    @5
    cA
    cA
    inxp
    @0
    @22
    @18
    @0
    @22
    cA
    @5
    cin
    @18
    cA
    @5
    incom
    cA
    @5
    @9
    cV
    cW
    @9
    eqid
    #
    @13
    ressbas
    syl5eqr
    sqxpeqd
    syl5eq
    oveq2d
    @0
    @4
    @20
    @19
    crest
    cA
    @4
    cW
    @9
    cV
    @23
    @14
    ressunif
    oveq1d
    @21
    @10
    wceq
    @0
    @18
    @20
    @9
    @18
    eqid
    @20
    eqid
    ussval
    a1i
    3eqtrd
    eqtr2d
end

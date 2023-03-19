include "wcel.mm"
include "cvv.mm"
include "cid.mm"
include "cxp.mm"
include "cin.mm"
include "cdiag2.mm"
include "cfv.mm"
include "wceq.mm"
include "elex.mm"
include "incom.mm"
include "sqxpexg.mm"
include "inex1g.mm"
include "syl.mm"
include "syl5eqelr.mm"
include "cv.mm"
include "id.mm"
include "sqxpeqd.mm"
include "ineq2d.mm"
include "df-bj-diag.mm"
include "fvmptg.mm"
include "syl2anc.mm"

theorem bj-diagval
  let cA: class A
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> ( Diag ` A ) = ( _I i^i ( A X. A ) ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cvv
    wcel
    cid
    cA
    cA
    cxp
    #
    cin
    #
    cvv
    wcel
    cA
    cdiag2
    cfv
    @2
    wceq
    cA
    cV
    elex
    @0
    @2
    @1
    cid
    cin
    #
    cvv
    @1
    cid
    incom
    @0
    @1
    cvv
    wcel
    @3
    cvv
    wcel
    cA
    cV
    sqxpexg
    @1
    cid
    cvv
    inex1g
    syl
    syl5eqelr
    vx
    cA
    cid
    vx
    cv
    #
    @4
    cxp
    #
    cin
    @2
    cvv
    cvv
    cdiag2
    @4
    cA
    wceq
    #
    @5
    @1
    cid
    @6
    @4
    cA
    @6
    id
    sqxpeqd
    ineq2d
    vx
    df-bj-diag
    fvmptg
    syl2anc
end

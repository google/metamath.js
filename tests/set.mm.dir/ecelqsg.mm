include "wcel.mm"
include "cec.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cqs.mm"
include "eqid.mm"
include "eceq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "cvv.mm"
include "wb.mm"
include "ecexg.mm"
include "elqsg.mm"
include "syl.mm"
include "biimpar.mm"
include "sylan2.mm"

theorem ecelqsg
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let vx: setvar x


  assert |- ( ( R e. V /\ B e. A ) -> [ B ] R e. ( A /. R ) )

  proof
    cB
    cA
    wcel
    #
    cR
    cV
    wcel
    #
    cB
    cR
    cec
    #
    vx
    cv
    #
    cR
    cec
    #
    wceq
    #
    vx
    cA
    wrex
    #
    @2
    cA
    cR
    cqs
    wcel
    #
    @0
    @2
    @2
    wceq
    #
    @6
    @2
    eqid
    @5
    @8
    vx
    cB
    cA
    @3
    cB
    wceq
    @4
    @2
    @2
    @3
    cB
    cR
    eceq1
    eqeq2d
    rspcev
    mpan2
    @1
    @7
    @6
    @1
    @2
    cvv
    wcel
    @7
    @6
    wb
    cB
    cV
    cR
    ecexg
    vx
    cA
    @2
    cR
    cvv
    elqsg
    syl
    biimpar
    sylan2
end

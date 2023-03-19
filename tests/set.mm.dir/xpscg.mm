include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "csn.mm"
include "cxp.mm"
include "c1o.mm"
include "cun.mm"
include "cop.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "cpr.mm"
include "wceq.mm"
include "cvv.mm"
include "0ex.mm"
include "xpsng.mm"
include "mpan.mm"
include "con0.mm"
include "1on.mm"
include "uneq12.mm"
include "syl2an.mm"
include "xpsc.mm"
include "df-pr.mm"
include "3eqtr4g.mm"

theorem xpscg
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> `' ( { A } +c { B } ) = { <. (/) , A >. , <. 1o , B >. } )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    c0
    csn
    cA
    csn
    #
    cxp
    #
    c1o
    csn
    cB
    csn
    #
    cxp
    #
    cun
    #
    c0
    cA
    cop
    #
    csn
    #
    c1o
    cB
    cop
    #
    csn
    #
    cun
    #
    @2
    @4
    ccda
    co
    ccnv
    @7
    @9
    cpr
    @0
    @3
    @8
    wceq
    #
    @5
    @10
    wceq
    #
    @6
    @11
    wceq
    @1
    c0
    cvv
    wcel
    @0
    @12
    0ex
    c0
    cA
    cvv
    cV
    xpsng
    mpan
    c1o
    con0
    wcel
    @1
    @13
    1on
    c1o
    cB
    con0
    cW
    xpsng
    mpan
    @3
    @8
    @5
    @10
    uneq12
    syl2an
    cA
    cB
    xpsc
    @7
    @9
    df-pr
    3eqtr4g
end

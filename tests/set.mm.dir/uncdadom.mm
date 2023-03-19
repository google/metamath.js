include "wcel.mm"
include "wa.mm"
include "cun.mm"
include "c0.mm"
include "csn.mm"
include "cxp.mm"
include "c1o.mm"
include "ccda.mm"
include "co.mm"
include "cdom.mm"
include "wbr.mm"
include "cen.mm"
include "cvv.mm"
include "0ex.mm"
include "xpsneng.mm"
include "mpan2.mm"
include "ensym.mm"
include "endom.mm"
include "3syl.mm"
include "con0.mm"
include "1on.mm"
include "cin.mm"
include "wceq.mm"
include "xp01disj.mm"
include "undom.mm"
include "syl2an.mm"
include "cdaval.mm"
include "breqtrrd.mm"

theorem uncdadom
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( A u. B ) ~<_ ( A +c B ) )

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
    cA
    cB
    cun
    #
    cA
    c0
    csn
    cxp
    #
    cB
    c1o
    csn
    cxp
    #
    cun
    #
    cA
    cB
    ccda
    co
    cdom
    @0
    cA
    @3
    cdom
    wbr
    #
    cB
    @4
    cdom
    wbr
    #
    @2
    @5
    cdom
    wbr
    #
    @1
    @0
    @3
    cA
    cen
    wbr
    #
    cA
    @3
    cen
    wbr
    @6
    @0
    c0
    cvv
    wcel
    @9
    0ex
    cA
    c0
    cV
    cvv
    xpsneng
    mpan2
    @3
    cA
    ensym
    cA
    @3
    endom
    3syl
    @1
    @4
    cB
    cen
    wbr
    #
    cB
    @4
    cen
    wbr
    @7
    @1
    c1o
    con0
    wcel
    @10
    1on
    cB
    c1o
    cW
    con0
    xpsneng
    mpan2
    @4
    cB
    ensym
    cB
    @4
    endom
    3syl
    @6
    @7
    wa
    @3
    @4
    cin
    c0
    wceq
    @8
    cA
    cB
    xp01disj
    cA
    @3
    cB
    @4
    undom
    mpan2
    syl2an
    cA
    cB
    cV
    cW
    cdaval
    breqtrrd
end

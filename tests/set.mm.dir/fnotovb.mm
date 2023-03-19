include "cxp.mm"
include "wfn.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "cotp.mm"
include "wb.mm"
include "wa.mm"
include "cop.mm"
include "wbr.mm"
include "fnbrovb.mm"
include "df-br.mm"
include "a1i.mm"
include "df-ot.mm"
include "eqcomi.mm"
include "eleq1i.mm"
include "3bitrd.mm"
include "3impb.mm"

theorem fnotovb
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cF: class F


  assert |- ( ( F Fn ( A X. B ) /\ C e. A /\ D e. B ) -> ( ( C F D ) = R <-> <. C , D , R >. e. F ) )

  proof
    cF
    cA
    cB
    cxp
    wfn
    #
    cC
    cA
    wcel
    #
    cD
    cB
    wcel
    #
    cC
    cD
    cF
    co
    cR
    wceq
    #
    cC
    cD
    cR
    cotp
    #
    cF
    wcel
    #
    wb
    @0
    @1
    @2
    wa
    wa
    #
    @3
    cC
    cD
    cop
    #
    cR
    cF
    wbr
    #
    @7
    cR
    cop
    #
    cF
    wcel
    #
    @5
    cC
    cD
    cR
    cF
    cA
    cB
    fnbrovb
    @8
    @10
    wb
    @6
    @7
    cR
    cF
    df-br
    a1i
    @10
    @5
    wb
    @6
    @9
    @4
    cF
    @4
    @9
    cC
    cD
    cR
    df-ot
    eqcomi
    eleq1i
    a1i
    3bitrd
    3impb
end

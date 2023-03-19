include "cxr.mm"
include "wcel.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "wb.mm"
include "xrleloe.mm"
include "3adant3.mm"
include "xrlttr.mm"
include "expd.mm"
include "breq1.mm"
include "biimprd.mm"
include "a1i.mm"
include "jaod.mm"
include "sylbid.mm"
include "impd.mm"

theorem xrlelttr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) -> ( ( A <_ B /\ B < C ) -> A < C ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    w3a
    #
    cA
    cB
    cle
    wbr
    #
    cB
    cC
    clt
    wbr
    #
    cA
    cC
    clt
    wbr
    #
    @3
    @4
    cA
    cB
    clt
    wbr
    #
    cA
    cB
    wceq
    #
    wo
    #
    @5
    @6
    wi
    #
    @0
    @1
    @4
    @9
    wb
    @2
    cA
    cB
    xrleloe
    3adant3
    @3
    @7
    @10
    @8
    @3
    @7
    @5
    @6
    cA
    cB
    cC
    xrlttr
    expd
    @8
    @10
    wi
    @3
    @8
    @6
    @5
    cA
    cB
    cC
    clt
    breq1
    biimprd
    a1i
    jaod
    sylbid
    impd
end

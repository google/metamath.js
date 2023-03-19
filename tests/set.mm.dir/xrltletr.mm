include "cxr.mm"
include "wcel.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "wb.mm"
include "xrleloe.mm"
include "3adant1.mm"
include "xrlttr.mm"
include "expcomd.mm"
include "breq2.mm"
include "biimpd.mm"
include "a1i.mm"
include "jaod.mm"
include "sylbid.mm"
include "com23.mm"
include "impd.mm"

theorem xrltletr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) -> ( ( A < B /\ B <_ C ) -> A < C ) )

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
    clt
    wbr
    #
    cB
    cC
    cle
    wbr
    #
    cA
    cC
    clt
    wbr
    #
    @3
    @5
    @4
    @6
    @3
    @5
    cB
    cC
    clt
    wbr
    #
    cB
    cC
    wceq
    #
    wo
    #
    @4
    @6
    wi
    #
    @1
    @2
    @5
    @9
    wb
    @0
    cB
    cC
    xrleloe
    3adant1
    @3
    @7
    @10
    @8
    @3
    @4
    @7
    @6
    cA
    cB
    cC
    xrlttr
    expcomd
    @8
    @10
    wi
    @3
    @8
    @4
    @6
    cB
    cC
    cA
    clt
    breq2
    biimpd
    a1i
    jaod
    sylbid
    com23
    impd
end

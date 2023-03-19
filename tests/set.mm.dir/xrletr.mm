include "cxr.mm"
include "wcel.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "clt.mm"
include "wceq.mm"
include "wo.mm"
include "wb.mm"
include "xrleloe.mm"
include "3adant1.mm"
include "adantr.mm"
include "xrlelttr.mm"
include "wi.mm"
include "xrltle.mm"
include "3adant2.mm"
include "syld.mm"
include "expdimp.mm"
include "breq2.mm"
include "biimpcd.mm"
include "adantl.mm"
include "jaod.mm"
include "sylbid.mm"
include "expimpd.mm"

theorem xrletr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) -> ( ( A <_ B /\ B <_ C ) -> A <_ C ) )

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
    cle
    wbr
    #
    cA
    cC
    cle
    wbr
    #
    @3
    @4
    wa
    #
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
    @6
    @3
    @5
    @10
    wb
    #
    @4
    @1
    @2
    @11
    @0
    cB
    cC
    xrleloe
    3adant1
    adantr
    @7
    @8
    @6
    @9
    @3
    @4
    @8
    @6
    @3
    @4
    @8
    wa
    cA
    cC
    clt
    wbr
    #
    @6
    cA
    cB
    cC
    xrlelttr
    @0
    @2
    @12
    @6
    wi
    @1
    cA
    cC
    xrltle
    3adant2
    syld
    expdimp
    @4
    @9
    @6
    wi
    @3
    @9
    @4
    @6
    cB
    cC
    cA
    cle
    breq2
    biimpcd
    adantl
    jaod
    sylbid
    expimpd
end

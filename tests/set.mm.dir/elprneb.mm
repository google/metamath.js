include "cpr.mm"
include "wcel.mm"
include "wne.mm"
include "wceq.mm"
include "wb.mm"
include "wo.mm"
include "wi.mm"
include "elpri.mm"
include "neeq1.mm"
include "eqcoms.mm"
include "pm5.1.mm"
include "ex.mm"
include "sylbid.mm"
include "neeq2.mm"
include "wa.mm"
include "wn.mm"
include "nesym.mm"
include "sylan2b.mm"
include "necon2abid.mm"
include "sylbird.mm"
include "jaoi.mm"
include "syl.mm"
include "imp.mm"

theorem elprneb
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. { B , C } /\ B =/= C ) -> ( A = B <-> A =/= C ) )

  proof
    cA
    cB
    cC
    cpr
    wcel
    #
    cB
    cC
    wne
    #
    cA
    cB
    wceq
    #
    cA
    cC
    wne
    #
    wb
    #
    @0
    @2
    cA
    cC
    wceq
    #
    wo
    @1
    @4
    wi
    #
    cA
    cB
    cC
    elpri
    @2
    @6
    @5
    @2
    @1
    @3
    @4
    @1
    @3
    wb
    cB
    cA
    cB
    cA
    cC
    neeq1
    eqcoms
    @2
    @3
    @4
    @2
    @3
    pm5.1
    ex
    sylbid
    @5
    @1
    cB
    cA
    wne
    #
    @4
    cA
    cC
    cB
    neeq2
    @5
    @7
    @4
    @5
    @7
    wa
    @2
    cA
    cC
    @7
    @5
    @2
    wn
    #
    @5
    @8
    wb
    cB
    cA
    nesym
    @5
    @8
    pm5.1
    sylan2b
    necon2abid
    ex
    sylbird
    jaoi
    syl
    imp
end

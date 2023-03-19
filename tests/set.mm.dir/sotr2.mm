include "wor.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "wb.mm"
include "sotric.mm"
include "ancom2s.mm"
include "3adantr3.mm"
include "con2bid.mm"
include "breq1.mm"
include "biimpd.mm"
include "a1i.mm"
include "sotr.mm"
include "expd.mm"
include "jaod.mm"
include "sylbird.mm"
include "impd.mm"

theorem sotr2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R


  assert |- ( ( R Or A /\ ( B e. A /\ C e. A /\ D e. A ) ) -> ( ( -. C R B /\ C R D ) -> B R D ) )

  proof
    cA
    cR
    wor
    #
    cB
    cA
    wcel
    #
    cC
    cA
    wcel
    #
    cD
    cA
    wcel
    #
    w3a
    wa
    #
    cC
    cB
    cR
    wbr
    #
    wn
    #
    cC
    cD
    cR
    wbr
    #
    cB
    cD
    cR
    wbr
    #
    @4
    @6
    cC
    cB
    wceq
    #
    cB
    cC
    cR
    wbr
    #
    wo
    #
    @7
    @8
    wi
    #
    @4
    @5
    @11
    @0
    @1
    @2
    @5
    @11
    wn
    wb
    #
    @3
    @0
    @2
    @1
    @13
    cA
    cC
    cB
    cR
    sotric
    ancom2s
    3adantr3
    con2bid
    @4
    @9
    @12
    @10
    @9
    @12
    wi
    @4
    @9
    @7
    @8
    cC
    cB
    cD
    cR
    breq1
    biimpd
    a1i
    @4
    @10
    @7
    @8
    cA
    cB
    cC
    cD
    cR
    sotr
    expd
    jaod
    sylbird
    impd
end

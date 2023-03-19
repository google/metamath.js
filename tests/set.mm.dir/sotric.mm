include "wor.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wbr.mm"
include "wo.mm"
include "wn.mm"
include "wi.mm"
include "sonr.mm"
include "breq2.mm"
include "notbid.mm"
include "syl5ibcom.mm"
include "adantrr.mm"
include "so2nr.mm"
include "imnan.mm"
include "sylibr.mm"
include "con2d.mm"
include "jaod.mm"
include "w3o.mm"
include "solin.mm"
include "3orass.mm"
include "sylib.mm"
include "ord.mm"
include "impbid.mm"
include "con2bid.mm"

theorem sotric
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R


  assert |- ( ( R Or A /\ ( B e. A /\ C e. A ) ) -> ( B R C <-> -. ( B = C \/ C R B ) ) )

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
    wa
    wa
    #
    cB
    cC
    wceq
    #
    cC
    cB
    cR
    wbr
    #
    wo
    #
    cB
    cC
    cR
    wbr
    #
    @3
    @6
    @7
    wn
    #
    @3
    @4
    @8
    @5
    @0
    @1
    @4
    @8
    wi
    @2
    @0
    @1
    wa
    cB
    cB
    cR
    wbr
    #
    wn
    @4
    @8
    cA
    cB
    cR
    sonr
    @4
    @9
    @7
    cB
    cC
    cB
    cR
    breq2
    notbid
    syl5ibcom
    adantrr
    @3
    @7
    @5
    @3
    @7
    @5
    wa
    wn
    @7
    @5
    wn
    wi
    cA
    cB
    cC
    cR
    so2nr
    @7
    @5
    imnan
    sylibr
    con2d
    jaod
    @3
    @7
    @6
    @3
    @7
    @4
    @5
    w3o
    @7
    @6
    wo
    cA
    cB
    cC
    cR
    solin
    @7
    @4
    @5
    3orass
    sylib
    ord
    impbid
    con2bid
end

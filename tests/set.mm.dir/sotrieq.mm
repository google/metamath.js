include "wor.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wo.mm"
include "wceq.mm"
include "wn.mm"
include "sonr.mm"
include "adantrr.mm"
include "pm1.2.mm"
include "nsyl.mm"
include "breq2.mm"
include "breq1.mm"
include "orbi12d.mm"
include "notbid.mm"
include "syl5ibcom.mm"
include "con2d.mm"
include "w3o.mm"
include "solin.mm"
include "3orass.mm"
include "sylib.mm"
include "or12.mm"
include "ord.mm"
include "impbid.mm"
include "con2bid.mm"

theorem sotrieq
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R


  assert |- ( ( R Or A /\ ( B e. A /\ C e. A ) ) -> ( B = C <-> -. ( B R C \/ C R B ) ) )

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
    cR
    wbr
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
    wceq
    #
    @3
    @6
    @7
    wn
    @3
    @7
    @6
    @3
    cB
    cB
    cR
    wbr
    #
    @8
    wo
    #
    wn
    @7
    @6
    wn
    @3
    @8
    @9
    @0
    @1
    @8
    wn
    @2
    cA
    cB
    cR
    sonr
    adantrr
    @8
    pm1.2
    nsyl
    @7
    @9
    @6
    @7
    @8
    @4
    @8
    @5
    cB
    cC
    cB
    cR
    breq2
    cB
    cC
    cB
    cR
    breq1
    orbi12d
    notbid
    syl5ibcom
    con2d
    @3
    @7
    @6
    @3
    @4
    @7
    @5
    wo
    wo
    #
    @7
    @6
    wo
    @3
    @4
    @7
    @5
    w3o
    @10
    cA
    cB
    cC
    cR
    solin
    @4
    @7
    @5
    3orass
    sylib
    @4
    @7
    @5
    or12
    sylib
    ord
    impbid
    con2bid
end

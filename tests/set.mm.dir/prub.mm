include "cnp.mm"
include "wcel.mm"
include "wa.mm"
include "cnq.mm"
include "wn.mm"
include "wceq.mm"
include "cltq.mm"
include "wbr.mm"
include "wo.mm"
include "wi.mm"
include "eleq1.mm"
include "biimpcd.mm"
include "adantl.mm"
include "prcdnq.mm"
include "jaod.mm"
include "con3d.mm"
include "adantr.mm"
include "wb.mm"
include "elprnq.mm"
include "wor.mm"
include "ltsonq.mm"
include "sotric.mm"
include "mpan.mm"
include "sylan.mm"
include "sylibrd.mm"

theorem prub
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. P. /\ B e. A ) /\ C e. Q. ) -> ( -. C e. A -> B <Q C ) )

  proof
    cA
    cnp
    wcel
    #
    cB
    cA
    wcel
    #
    wa
    #
    cC
    cnq
    wcel
    #
    wa
    cC
    cA
    wcel
    #
    wn
    #
    cB
    cC
    wceq
    #
    cC
    cB
    cltq
    wbr
    #
    wo
    #
    wn
    #
    cB
    cC
    cltq
    wbr
    #
    @2
    @5
    @9
    wi
    @3
    @2
    @8
    @4
    @2
    @6
    @4
    @7
    @1
    @6
    @4
    wi
    @0
    @6
    @1
    @4
    cB
    cC
    cA
    eleq1
    biimpcd
    adantl
    cA
    cB
    cC
    prcdnq
    jaod
    con3d
    adantr
    @2
    cB
    cnq
    wcel
    #
    @3
    @10
    @9
    wb
    #
    cA
    cB
    elprnq
    cnq
    cltq
    wor
    @11
    @3
    wa
    @12
    ltsonq
    cnq
    cB
    cC
    cltq
    sotric
    mpan
    sylan
    sylibrd
end

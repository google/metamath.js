include "cen.mm"
include "wbr.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "wne.mm"
include "wn.mm"
include "wpss.mm"
include "df-pss.mm"
include "pssinf.mm"
include "expcom.mm"
include "syl5bir.mm"
include "expdimp.mm"
include "necon4ad.mm"
include "3impia.mm"
include "3com13.mm"

theorem fisseneq
  let cA: class A
  let cB: class B


  assert |- ( ( B e. Fin /\ A C_ B /\ A ~~ B ) -> A = B )

  proof
    cA
    cB
    cen
    wbr
    #
    cA
    cB
    wss
    #
    cB
    cfn
    wcel
    #
    cA
    cB
    wceq
    #
    @0
    @1
    @2
    @3
    @0
    @1
    wa
    @2
    cA
    cB
    @0
    @1
    cA
    cB
    wne
    #
    @2
    wn
    #
    @1
    @4
    wa
    cA
    cB
    wpss
    #
    @0
    @5
    cA
    cB
    df-pss
    @6
    @0
    @5
    cA
    cB
    pssinf
    expcom
    syl5bir
    expdimp
    necon4ad
    3impia
    3com13
end

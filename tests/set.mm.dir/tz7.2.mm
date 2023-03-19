include "wtr.mm"
include "cep.mm"
include "wfr.mm"
include "wcel.mm"
include "wss.mm"
include "wne.mm"
include "wa.mm"
include "trss.mm"
include "wn.mm"
include "wceq.mm"
include "efrirr.mm"
include "eleq1.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "necon2ad.mm"
include "anim12ii.mm"
include "3impia.mm"

theorem tz7.2
  let cA: class A
  let cB: class B


  assert |- ( ( Tr A /\ _E Fr A /\ B e. A ) -> ( B C_ A /\ B =/= A ) )

  proof
    cA
    wtr
    #
    cA
    cep
    wfr
    #
    cB
    cA
    wcel
    #
    cB
    cA
    wss
    #
    cB
    cA
    wne
    #
    wa
    @0
    @2
    @3
    @1
    @4
    cA
    cB
    trss
    @1
    @2
    cB
    cA
    @1
    @2
    wn
    cB
    cA
    wceq
    #
    cA
    cA
    wcel
    #
    wn
    cA
    efrirr
    @5
    @2
    @6
    cB
    cA
    cA
    eleq1
    notbid
    syl5ibrcom
    necon2ad
    anim12ii
    3impia
end

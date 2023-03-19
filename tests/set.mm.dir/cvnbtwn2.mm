include "cch.mm"
include "wcel.mm"
include "w3a.mm"
include "ccv.mm"
include "wbr.mm"
include "wpss.mm"
include "wa.mm"
include "wn.mm"
include "wss.mm"
include "wceq.mm"
include "wi.mm"
include "cvnbtwn.mm"
include "iman.mm"
include "anass.mm"
include "dfpss2.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "notbii.mm"
include "bitr2i.mm"
include "syl6ib.mm"

theorem cvnbtwn2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CH /\ B e. CH /\ C e. CH ) -> ( A <oH B -> ( ( A C. C /\ C C_ B ) -> C = B ) ) )

  proof
    cA
    cch
    wcel
    cB
    cch
    wcel
    cC
    cch
    wcel
    w3a
    cA
    cB
    ccv
    wbr
    cA
    cC
    wpss
    #
    cC
    cB
    wpss
    #
    wa
    #
    wn
    #
    @0
    cC
    cB
    wss
    #
    wa
    #
    cC
    cB
    wceq
    #
    wi
    #
    cA
    cB
    cC
    cvnbtwn
    @7
    @5
    @6
    wn
    #
    wa
    #
    wn
    @3
    @5
    @6
    iman
    @9
    @2
    @9
    @0
    @4
    @8
    wa
    #
    wa
    @2
    @0
    @4
    @8
    anass
    @1
    @10
    @0
    cC
    cB
    dfpss2
    anbi2i
    bitr4i
    notbii
    bitr2i
    syl6ib
end

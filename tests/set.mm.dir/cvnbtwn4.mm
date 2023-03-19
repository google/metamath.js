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
include "wo.mm"
include "wi.mm"
include "cvnbtwn.mm"
include "iman.mm"
include "an4.mm"
include "ioran.mm"
include "eqcom.mm"
include "notbii.mm"
include "anbi1i.mm"
include "bitri.mm"
include "anbi2i.mm"
include "dfpss2.mm"
include "anbi12i.mm"
include "3bitr4i.mm"
include "bitr2i.mm"
include "syl6ib.mm"

theorem cvnbtwn4
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CH /\ B e. CH /\ C e. CH ) -> ( A <oH B -> ( ( A C_ C /\ C C_ B ) -> ( C = A \/ C = B ) ) ) )

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
    cA
    cC
    wss
    #
    cC
    cB
    wss
    #
    wa
    #
    cC
    cA
    wceq
    #
    cC
    cB
    wceq
    #
    wo
    #
    wi
    #
    cA
    cB
    cC
    cvnbtwn
    @10
    @6
    @9
    wn
    #
    wa
    #
    wn
    @3
    @6
    @9
    iman
    @12
    @2
    @6
    cA
    cC
    wceq
    #
    wn
    #
    @8
    wn
    #
    wa
    #
    wa
    @4
    @14
    wa
    #
    @5
    @15
    wa
    #
    wa
    @12
    @2
    @4
    @5
    @14
    @15
    an4
    @11
    @16
    @6
    @11
    @7
    wn
    #
    @15
    wa
    @16
    @7
    @8
    ioran
    @19
    @14
    @15
    @7
    @13
    cC
    cA
    eqcom
    notbii
    anbi1i
    bitri
    anbi2i
    @0
    @17
    @1
    @18
    cA
    cC
    dfpss2
    cC
    cB
    dfpss2
    anbi12i
    3bitr4i
    notbii
    bitr2i
    syl6ib
end

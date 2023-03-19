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
include "eqcom.mm"
include "imbi2i.mm"
include "dfpss2.mm"
include "anbi1i.mm"
include "an32.mm"
include "bitri.mm"
include "notbii.mm"
include "3bitr4ri.mm"
include "syl6ib.mm"

theorem cvnbtwn3
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CH /\ B e. CH /\ C e. CH ) -> ( A <oH B -> ( ( A C_ C /\ C C. B ) -> C = A ) ) )

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
    @1
    wa
    #
    cC
    cA
    wceq
    #
    wi
    #
    cA
    cB
    cC
    cvnbtwn
    @5
    cA
    cC
    wceq
    #
    wi
    @5
    @8
    wn
    #
    wa
    #
    wn
    @7
    @3
    @5
    @8
    iman
    @6
    @8
    @5
    cC
    cA
    eqcom
    imbi2i
    @2
    @10
    @2
    @4
    @9
    wa
    #
    @1
    wa
    @10
    @0
    @11
    @1
    cA
    cC
    dfpss2
    anbi1i
    @4
    @9
    @1
    an32
    bitri
    notbii
    3bitr4ri
    syl6ib
end

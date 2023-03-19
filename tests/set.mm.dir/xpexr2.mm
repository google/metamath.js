include "cxp.mm"
include "c0.mm"
include "wne.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "xpnz.mm"
include "cdm.mm"
include "wceq.mm"
include "dmxp.mm"
include "adantl.mm"
include "dmexg.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "crn.mm"
include "rnxp.mm"
include "rnexg.mm"
include "anim12dan.mm"
include "ancom2s.mm"
include "sylan2br.mm"

theorem xpexr2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A X. B ) e. C /\ ( A X. B ) =/= (/) ) -> ( A e. _V /\ B e. _V ) )

  proof
    cA
    cB
    cxp
    #
    c0
    wne
    @0
    cC
    wcel
    #
    cA
    c0
    wne
    #
    cB
    c0
    wne
    #
    wa
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    #
    cA
    cB
    xpnz
    @1
    @3
    @2
    @6
    @1
    @3
    @4
    @2
    @5
    @1
    @3
    wa
    @0
    cdm
    #
    cA
    cvv
    @3
    @7
    cA
    wceq
    @1
    cA
    cB
    dmxp
    adantl
    @1
    @7
    cvv
    wcel
    @3
    @0
    cC
    dmexg
    adantr
    eqeltrrd
    @1
    @2
    wa
    @0
    crn
    #
    cB
    cvv
    @2
    @8
    cB
    wceq
    @1
    cA
    cB
    rnxp
    adantl
    @1
    @8
    cvv
    wcel
    @2
    @0
    cC
    rnexg
    adantr
    eqeltrrd
    anim12dan
    ancom2s
    sylan2br
end

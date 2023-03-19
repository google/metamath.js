include "cxp.mm"
include "wcel.mm"
include "cvv.mm"
include "wn.mm"
include "wi.mm"
include "c0.mm"
include "wceq.mm"
include "0ex.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "pm2.24d.mm"
include "a1d.mm"
include "wne.mm"
include "crn.mm"
include "rnexg.mm"
include "rnxp.mm"
include "eleq1d.mm"
include "syl5ib.mm"
include "a1dd.mm"
include "pm2.61ine.mm"
include "orrd.mm"

theorem xpexr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A X. B ) e. C -> ( A e. _V \/ B e. _V ) )

  proof
    cA
    cB
    cxp
    #
    cC
    wcel
    #
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    @1
    @2
    wn
    #
    @3
    wi
    #
    wi
    cA
    c0
    cA
    c0
    wceq
    #
    @5
    @1
    @6
    @2
    @3
    @6
    @2
    c0
    cvv
    wcel
    0ex
    cA
    c0
    cvv
    eleq1
    mpbiri
    pm2.24d
    a1d
    cA
    c0
    wne
    #
    @1
    @3
    @4
    @1
    @0
    crn
    #
    cvv
    wcel
    @7
    @3
    @0
    cC
    rnexg
    @7
    @8
    cB
    cvv
    cA
    cB
    rnxp
    eleq1d
    syl5ib
    a1dd
    pm2.61ine
    orrd
end

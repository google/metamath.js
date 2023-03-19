include "c0.mm"
include "wne.mm"
include "cxp.mm"
include "wcel.mm"
include "cvv.mm"
include "wi.mm"
include "wceq.mm"
include "0ex.mm"
include "eleq1a.mm"
include "ax-mp.mm"
include "a1d.mm"
include "wa.mm"
include "xpnz.mm"
include "xpexr2.mm"
include "simprd.mm"
include "expcom.mm"
include "sylbi.mm"
include "pm2.61ine.mm"

theorem bj-xpnzex
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A =/= (/) -> ( ( A X. B ) e. V -> B e. _V ) )

  proof
    cA
    c0
    wne
    #
    cA
    cB
    cxp
    #
    cV
    wcel
    #
    cB
    cvv
    wcel
    #
    wi
    #
    wi
    cB
    c0
    cB
    c0
    wceq
    #
    @4
    @0
    @5
    @3
    @2
    c0
    cvv
    wcel
    @5
    @3
    wi
    0ex
    c0
    cvv
    cB
    eleq1a
    ax-mp
    a1d
    a1d
    @0
    cB
    c0
    wne
    #
    @4
    @0
    @6
    wa
    @1
    c0
    wne
    #
    @4
    cA
    cB
    xpnz
    @2
    @7
    @3
    @2
    @7
    wa
    cA
    cvv
    wcel
    @3
    cA
    cB
    cV
    xpexr2
    simprd
    expcom
    sylbi
    expcom
    pm2.61ine
end

include "cxp.mm"
include "c0.mm"
include "wceq.mm"
include "wne.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "xpnz.mm"
include "necon2bbii.mm"
include "ianor.mm"
include "nne.mm"
include "orbi12i.mm"
include "3bitri.mm"

theorem xpeq0
  let cA: class A
  let cB: class B


  assert |- ( ( A X. B ) = (/) <-> ( A = (/) \/ B = (/) ) )

  proof
    cA
    cB
    cxp
    #
    c0
    wceq
    cA
    c0
    wne
    #
    cB
    c0
    wne
    #
    wa
    #
    wn
    @1
    wn
    #
    @2
    wn
    #
    wo
    cA
    c0
    wceq
    #
    cB
    c0
    wceq
    #
    wo
    @3
    @0
    c0
    cA
    cB
    xpnz
    necon2bbii
    @1
    @2
    ianor
    @4
    @6
    @5
    @7
    cA
    c0
    nne
    cB
    c0
    nne
    orbi12i
    3bitri
end

include "cin.mm"
include "c0.mm"
include "wne.mm"
include "cxp.mm"
include "cima.mm"
include "wceq.mm"
include "cif.mm"
include "xpima.mm"
include "ifnefalse.mm"
include "syl5eq.mm"

theorem xpima2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A i^i C ) =/= (/) -> ( ( A X. B ) " C ) = B )

  proof
    cA
    cC
    cin
    #
    c0
    wne
    cA
    cB
    cxp
    cC
    cima
    @0
    c0
    wceq
    c0
    cB
    cif
    cB
    cA
    cB
    cC
    xpima
    @0
    c0
    c0
    cB
    ifnefalse
    syl5eq
end

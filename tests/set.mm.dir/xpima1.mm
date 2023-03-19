include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cxp.mm"
include "cima.mm"
include "cif.mm"
include "xpima.mm"
include "iftrue.mm"
include "syl5eq.mm"

theorem xpima1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A i^i C ) = (/) -> ( ( A X. B ) " C ) = (/) )

  proof
    cA
    cC
    cin
    c0
    wceq
    #
    cA
    cB
    cxp
    cC
    cima
    @0
    c0
    cB
    cif
    c0
    cA
    cB
    cC
    xpima
    @0
    c0
    cB
    iftrue
    syl5eq
end

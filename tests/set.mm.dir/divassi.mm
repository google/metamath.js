include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "wceq.mm"
include "divasszi.mm"
include "ax-mp.mm"

theorem divassi
  let cA: class A
  let cB: class B
  let cC: class C
  assume divclz.1: |- A e. CC
  assume divclz.2: |- B e. CC
  assume divmulz.3: |- C e. CC
  assume divass.4: |- C =/= 0


  assert |- ( ( A x. B ) / C ) = ( A x. ( B / C ) )

  proof
    cC
    cc0
    wne
    cA
    cB
    cmul
    co
    cC
    cdiv
    co
    cA
    cB
    cC
    cdiv
    co
    cmul
    co
    wceq
    divass.4
    cA
    cB
    cC
    divclz.1
    divclz.2
    divmulz.3
    divasszi
    ax-mp
end

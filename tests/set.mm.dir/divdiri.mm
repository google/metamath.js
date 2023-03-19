include "cc0.mm"
include "wne.mm"
include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "wceq.mm"
include "divdirzi.mm"
include "ax-mp.mm"

theorem divdiri
  let cA: class A
  let cB: class B
  let cC: class C
  assume divclz.1: |- A e. CC
  assume divclz.2: |- B e. CC
  assume divmulz.3: |- C e. CC
  assume divass.4: |- C =/= 0


  assert |- ( ( A + B ) / C ) = ( ( A / C ) + ( B / C ) )

  proof
    cC
    cc0
    wne
    cA
    cB
    caddc
    co
    cC
    cdiv
    co
    cA
    cC
    cdiv
    co
    cB
    cC
    cdiv
    co
    caddc
    co
    wceq
    divass.4
    cA
    cB
    cC
    divclz.1
    divclz.2
    divmulz.3
    divdirzi
    ax-mp
end

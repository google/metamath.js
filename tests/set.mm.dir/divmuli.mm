include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cmul.mm"
include "wb.mm"
include "divmulzi.mm"
include "ax-mp.mm"

theorem divmuli
  let cA: class A
  let cB: class B
  let cC: class C
  assume divclz.1: |- A e. CC
  assume divclz.2: |- B e. CC
  assume divmulz.3: |- C e. CC
  assume divmul.4: |- B =/= 0


  assert |- ( ( A / B ) = C <-> ( B x. C ) = A )

  proof
    cB
    cc0
    wne
    cA
    cB
    cdiv
    co
    cC
    wceq
    cB
    cC
    cmul
    co
    cA
    wceq
    wb
    divmul.4
    cA
    cB
    cC
    divclz.1
    divclz.2
    divmulz.3
    divmulzi
    ax-mp
end

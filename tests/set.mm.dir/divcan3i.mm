include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "wceq.mm"
include "divcan3zi.mm"
include "ax-mp.mm"

theorem divcan3i
  let cA: class A
  let cB: class B
  assume divclz.1: |- A e. CC
  assume divclz.2: |- B e. CC
  assume divcl.3: |- B =/= 0


  assert |- ( ( B x. A ) / B ) = A

  proof
    cB
    cc0
    wne
    cB
    cA
    cmul
    co
    cB
    cdiv
    co
    cA
    wceq
    divcl.3
    cA
    cB
    divclz.1
    divclz.2
    divcan3zi
    ax-mp
end

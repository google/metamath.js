include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "divcan2zi.mm"
include "ax-mp.mm"

theorem divcan2i
  let cA: class A
  let cB: class B
  assume divclz.1: |- A e. CC
  assume divclz.2: |- B e. CC
  assume divcl.3: |- B =/= 0


  assert |- ( B x. ( A / B ) ) = A

  proof
    cB
    cc0
    wne
    cB
    cA
    cB
    cdiv
    co
    cmul
    co
    cA
    wceq
    divcl.3
    cA
    cB
    divclz.1
    divclz.2
    divcan2zi
    ax-mp
end

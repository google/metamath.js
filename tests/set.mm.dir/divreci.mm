include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "cmul.mm"
include "wceq.mm"
include "divreczi.mm"
include "ax-mp.mm"

theorem divreci
  let cA: class A
  let cB: class B
  assume divclz.1: |- A e. CC
  assume divclz.2: |- B e. CC
  assume divcl.3: |- B =/= 0


  assert |- ( A / B ) = ( A x. ( 1 / B ) )

  proof
    cB
    cc0
    wne
    cA
    cB
    cdiv
    co
    cA
    c1
    cB
    cdiv
    co
    cmul
    co
    wceq
    divcl.3
    cA
    cB
    divclz.1
    divclz.2
    divreczi
    ax-mp
end

include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "cc.mm"
include "wcel.mm"
include "divclzi.mm"
include "ax-mp.mm"

theorem divcli
  let cA: class A
  let cB: class B
  assume divclz.1: |- A e. CC
  assume divclz.2: |- B e. CC
  assume divcl.3: |- B =/= 0


  assert |- ( A / B ) e. CC

  proof
    cB
    cc0
    wne
    cA
    cB
    cdiv
    co
    cc
    wcel
    divcl.3
    cA
    cB
    divclz.1
    divclz.2
    divclzi
    ax-mp
end

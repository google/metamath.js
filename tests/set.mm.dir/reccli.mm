include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cc.mm"
include "wcel.mm"
include "recclzi.mm"
include "ax-mp.mm"

theorem reccli
  let cA: class A
  assume divclz.1: |- A e. CC
  assume reccl.2: |- A =/= 0


  assert |- ( 1 / A ) e. CC

  proof
    cA
    cc0
    wne
    c1
    cA
    cdiv
    co
    cc
    wcel
    reccl.2
    cA
    divclz.1
    recclzi
    ax-mp
end

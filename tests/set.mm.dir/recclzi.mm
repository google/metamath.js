include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "reccl.mm"
include "mpan.mm"

theorem recclzi
  let cA: class A
  assume divclz.1: |- A e. CC


  assert |- ( A =/= 0 -> ( 1 / A ) e. CC )

  proof
    cA
    cc
    wcel
    cA
    cc0
    wne
    c1
    cA
    cdiv
    co
    cc
    wcel
    divclz.1
    cA
    reccl
    mpan
end

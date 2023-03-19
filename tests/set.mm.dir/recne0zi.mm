include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "recne0.mm"
include "mpan.mm"

theorem recne0zi
  let cA: class A
  assume divclz.1: |- A e. CC


  assert |- ( A =/= 0 -> ( 1 / A ) =/= 0 )

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
    cc0
    wne
    divclz.1
    cA
    recne0
    mpan
end

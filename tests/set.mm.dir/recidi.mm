include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "recidzi.mm"
include "ax-mp.mm"

theorem recidi
  let cA: class A
  assume divclz.1: |- A e. CC
  assume reccl.2: |- A =/= 0


  assert |- ( A x. ( 1 / A ) ) = 1

  proof
    cA
    cc0
    wne
    cA
    c1
    cA
    cdiv
    co
    cmul
    co
    c1
    wceq
    reccl.2
    cA
    divclz.1
    recidzi
    ax-mp
end

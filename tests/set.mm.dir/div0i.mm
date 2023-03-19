include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "div0.mm"
include "mp2an.mm"

theorem div0i
  let cA: class A
  assume divclz.1: |- A e. CC
  assume reccl.2: |- A =/= 0


  assert |- ( 0 / A ) = 0

  proof
    cA
    cc
    wcel
    cA
    cc0
    wne
    cc0
    cA
    cdiv
    co
    cc0
    wceq
    divclz.1
    reccl.2
    cA
    div0
    mp2an
end

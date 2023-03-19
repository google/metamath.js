include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "divid.mm"
include "mp2an.mm"

theorem dividi
  let cA: class A
  assume divclz.1: |- A e. CC
  assume reccl.2: |- A =/= 0


  assert |- ( A / A ) = 1

  proof
    cA
    cc
    wcel
    cA
    cc0
    wne
    cA
    cA
    cdiv
    co
    c1
    wceq
    divclz.1
    reccl.2
    cA
    divid
    mp2an
end

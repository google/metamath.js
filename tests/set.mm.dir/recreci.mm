include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "recrec.mm"
include "mp2an.mm"

theorem recreci
  let cA: class A
  assume divclz.1: |- A e. CC
  assume reccl.2: |- A =/= 0


  assert |- ( 1 / ( 1 / A ) ) = A

  proof
    cA
    cc
    wcel
    cA
    cc0
    wne
    c1
    c1
    cA
    cdiv
    co
    cdiv
    co
    cA
    wceq
    divclz.1
    reccl.2
    cA
    recrec
    mp2an
end

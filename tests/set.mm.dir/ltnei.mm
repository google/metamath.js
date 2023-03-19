include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "wne.mm"
include "ltne.mm"
include "mpan.mm"

theorem ltnei
  let cA: class A
  let cB: class B
  assume lt.1: |- A e. RR
  assume lt.2: |- B e. RR


  assert |- ( A < B -> B =/= A )

  proof
    cA
    cr
    wcel
    cA
    cB
    clt
    wbr
    cB
    cA
    wne
    lt.1
    cA
    cB
    ltne
    mpan
end

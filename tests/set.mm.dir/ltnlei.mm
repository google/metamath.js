include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "lenlti.mm"
include "con2bii.mm"

theorem ltnlei
  let cA: class A
  let cB: class B
  assume lt.1: |- A e. RR
  assume lt.2: |- B e. RR


  assert |- ( A < B <-> -. B <_ A )

  proof
    cB
    cA
    cle
    wbr
    cA
    cB
    clt
    wbr
    cB
    cA
    lt.2
    lt.1
    lenlti
    con2bii
end

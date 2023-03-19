include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "divgt0i2i.mm"
include "ax-mp.mm"

theorem divgt0ii
  let cA: class A
  let cB: class B
  assume ltplus1.1: |- A e. RR
  assume prodgt0.2: |- B e. RR
  assume ltreci.3: |- 0 < A
  assume ltreci.4: |- 0 < B


  assert |- 0 < ( A / B )

  proof
    cc0
    cA
    clt
    wbr
    cc0
    cA
    cB
    cdiv
    co
    clt
    wbr
    ltreci.3
    cA
    cB
    ltplus1.1
    prodgt0.2
    ltreci.4
    divgt0i2i
    ax-mp
end

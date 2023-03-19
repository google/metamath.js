include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "ltlei.mm"
include "ax-mp.mm"

theorem ltleii
  let cA: class A
  let cB: class B
  assume lt.1: |- A e. RR
  assume lt.2: |- B e. RR
  assume ltlei.1: |- A < B


  assert |- A <_ B

  proof
    cA
    cB
    clt
    wbr
    cA
    cB
    cle
    wbr
    ltlei.1
    cA
    cB
    lt.1
    lt.2
    ltlei
    ax-mp
end

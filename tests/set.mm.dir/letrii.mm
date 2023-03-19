include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "clt.mm"
include "ltnlei.mm"
include "ltlei.mm"
include "sylbir.mm"
include "orri.mm"

theorem letrii
  let cA: class A
  let cB: class B
  assume lt.1: |- A e. RR
  assume lt.2: |- B e. RR


  assert |- ( A <_ B \/ B <_ A )

  proof
    cA
    cB
    cle
    wbr
    #
    cB
    cA
    cle
    wbr
    #
    @0
    wn
    cB
    cA
    clt
    wbr
    @1
    cB
    cA
    lt.2
    lt.1
    ltnlei
    cB
    cA
    lt.2
    lt.1
    ltlei
    sylbir
    orri
end

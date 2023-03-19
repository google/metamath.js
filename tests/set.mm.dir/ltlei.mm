include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wi.mm"
include "ltle.mm"
include "mp2an.mm"

theorem ltlei
  let cA: class A
  let cB: class B
  assume lt.1: |- A e. RR
  assume lt.2: |- B e. RR


  assert |- ( A < B -> A <_ B )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    clt
    wbr
    cA
    cB
    cle
    wbr
    wi
    lt.1
    lt.2
    cA
    cB
    ltle
    mp2an
end

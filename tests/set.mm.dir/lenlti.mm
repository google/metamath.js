include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "wb.mm"
include "lenlt.mm"
include "mp2an.mm"

theorem lenlti
  let cA: class A
  let cB: class B
  assume lt.1: |- A e. RR
  assume lt.2: |- B e. RR


  assert |- ( A <_ B <-> -. B < A )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    cle
    wbr
    cB
    cA
    clt
    wbr
    wn
    wb
    lt.1
    lt.2
    cA
    cB
    lenlt
    mp2an
end

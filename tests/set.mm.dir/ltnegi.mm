include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "wb.mm"
include "ltneg.mm"
include "mp2an.mm"

theorem ltnegi
  let cA: class A
  let cB: class B
  assume lt2.1: |- A e. RR
  assume lt2.2: |- B e. RR


  assert |- ( A < B <-> -u B < -u A )

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
    cB
    cneg
    cA
    cneg
    clt
    wbr
    wb
    lt2.1
    lt2.2
    cA
    cB
    ltneg
    mp2an
end

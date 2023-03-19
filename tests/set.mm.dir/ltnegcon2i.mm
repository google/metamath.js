include "cr.mm"
include "wcel.mm"
include "cneg.mm"
include "clt.mm"
include "wbr.mm"
include "wb.mm"
include "ltnegcon2.mm"
include "mp2an.mm"

theorem ltnegcon2i
  let cA: class A
  let cB: class B
  assume lt2.1: |- A e. RR
  assume lt2.2: |- B e. RR


  assert |- ( A < -u B <-> B < -u A )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    cneg
    clt
    wbr
    cB
    cA
    cneg
    clt
    wbr
    wb
    lt2.1
    lt2.2
    cA
    cB
    ltnegcon2
    mp2an
end

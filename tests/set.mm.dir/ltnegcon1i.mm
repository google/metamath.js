include "cr.mm"
include "wcel.mm"
include "cneg.mm"
include "clt.mm"
include "wbr.mm"
include "wb.mm"
include "ltnegcon1.mm"
include "mp2an.mm"

theorem ltnegcon1i
  let cA: class A
  let cB: class B
  assume lt2.1: |- A e. RR
  assume lt2.2: |- B e. RR


  assert |- ( -u A < B <-> -u B < A )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cneg
    cB
    clt
    wbr
    cB
    cneg
    cA
    clt
    wbr
    wb
    lt2.1
    lt2.2
    cA
    cB
    ltnegcon1
    mp2an
end

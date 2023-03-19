include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "wb.mm"
include "leneg.mm"
include "mp2an.mm"

theorem lenegi
  let cA: class A
  let cB: class B
  assume lt2.1: |- A e. RR
  assume lt2.2: |- B e. RR


  assert |- ( A <_ B <-> -u B <_ -u A )

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
    cneg
    cA
    cneg
    cle
    wbr
    wb
    lt2.1
    lt2.2
    cA
    cB
    leneg
    mp2an
end

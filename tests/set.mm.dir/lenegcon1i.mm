include "cr.mm"
include "wcel.mm"
include "cneg.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "lenegcon1.mm"
include "mp2an.mm"

theorem lenegcon1i
  let cA: class A
  let cB: class B
  assume lt2.1: |- A e. RR
  assume lt2.2: |- B e. RR


  assert |- ( -u A <_ B <-> -u B <_ A )

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
    cle
    wbr
    cB
    cneg
    cA
    cle
    wbr
    wb
    lt2.1
    lt2.2
    cA
    cB
    lenegcon1
    mp2an
end

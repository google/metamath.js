include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "subge0.mm"
include "mp2an.mm"

theorem subge0i
  let cA: class A
  let cB: class B
  assume lt2.1: |- A e. RR
  assume lt2.2: |- B e. RR


  assert |- ( 0 <_ ( A - B ) <-> B <_ A )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cc0
    cA
    cB
    cmin
    co
    cle
    wbr
    cB
    cA
    cle
    wbr
    wb
    lt2.1
    lt2.2
    cA
    cB
    subge0
    mp2an
end

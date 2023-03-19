include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "wa.mm"
include "wceq.mm"
include "wb.mm"
include "lesub0.mm"
include "mp2an.mm"

theorem lesub0i
  let cA: class A
  let cB: class B
  assume lt2.1: |- A e. RR
  assume lt2.2: |- B e. RR


  assert |- ( ( 0 <_ A /\ B <_ ( B - A ) ) <-> A = 0 )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cc0
    cA
    cle
    wbr
    cB
    cB
    cA
    cmin
    co
    cle
    wbr
    wa
    cA
    cc0
    wceq
    wb
    lt2.1
    lt2.2
    cA
    cB
    lesub0
    mp2an
end

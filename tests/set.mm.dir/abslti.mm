include "cr.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "wa.mm"
include "wb.mm"
include "abslt.mm"
include "mp2an.mm"

theorem abslti
  let cA: class A
  let cB: class B
  assume sqrth.1: |- A e. RR
  assume sqr11.1: |- B e. RR


  assert |- ( ( abs ` A ) < B <-> ( -u B < A /\ A < B ) )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cabs
    cfv
    cB
    clt
    wbr
    cB
    cneg
    cA
    clt
    wbr
    cA
    cB
    clt
    wbr
    wa
    wb
    sqrth.1
    sqr11.1
    cA
    cB
    abslt
    mp2an
end

include "cr.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "wa.mm"
include "wb.mm"
include "absle.mm"
include "mp2an.mm"

theorem abslei
  let cA: class A
  let cB: class B
  assume sqrth.1: |- A e. RR
  assume sqr11.1: |- B e. RR


  assert |- ( ( abs ` A ) <_ B <-> ( -u B <_ A /\ A <_ B ) )

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
    cle
    wbr
    cB
    cneg
    cA
    cle
    wbr
    cA
    cB
    cle
    wbr
    wa
    wb
    sqrth.1
    sqr11.1
    cA
    cB
    absle
    mp2an
end

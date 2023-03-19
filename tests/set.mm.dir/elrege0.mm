include "cc0.mm"
include "cr.mm"
include "wcel.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wb.mm"
include "0re.mm"
include "elicopnf.mm"
include "ax-mp.mm"

theorem elrege0
  let cA: class A


  assert |- ( A e. ( 0 [,) +oo ) <-> ( A e. RR /\ 0 <_ A ) )

  proof
    cc0
    cr
    wcel
    cA
    cc0
    cpnf
    cico
    co
    wcel
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    wa
    wb
    0re
    cc0
    cA
    elicopnf
    ax-mp
end

include "c1.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "1re.mm"
include "0le1.mm"
include "absid.mm"
include "mp2an.mm"

theorem abs1



  assert |- ( abs ` 1 ) = 1

  proof
    c1
    cr
    wcel
    cc0
    c1
    cle
    wbr
    c1
    cabs
    cfv
    c1
    wceq
    1re
    0le1
    c1
    absid
    mp2an
end

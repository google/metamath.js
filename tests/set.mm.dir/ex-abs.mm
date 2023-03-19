include "c2.mm"
include "cneg.mm"
include "cabs.mm"
include "cfv.mm"
include "2cn.mm"
include "absnegi.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "2re.mm"
include "0le2.mm"
include "absid.mm"
include "mp2an.mm"
include "eqtri.mm"

theorem ex-abs



  assert |- ( abs ` -u 2 ) = 2

  proof
    c2
    cneg
    cabs
    cfv
    c2
    cabs
    cfv
    #
    c2
    c2
    2cn
    absnegi
    c2
    cr
    wcel
    cc0
    c2
    cle
    wbr
    @0
    c2
    wceq
    2re
    0le2
    c2
    absid
    mp2an
    eqtri
end

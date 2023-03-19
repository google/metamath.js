include "cii.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "crest.mm"
include "cconn.mm"
include "dfii2.mm"
include "cr.mm"
include "wcel.mm"
include "0re.mm"
include "1re.mm"
include "iccconn.mm"
include "mp2an.mm"
include "eqeltri.mm"

theorem iiconn



  assert |- II e. Conn

  proof
    cii
    cioo
    crn
    ctg
    cfv
    cc0
    c1
    cicc
    co
    crest
    co
    #
    cconn
    dfii2
    cc0
    cr
    wcel
    c1
    cr
    wcel
    @0
    cconn
    wcel
    0re
    1re
    cc0
    c1
    iccconn
    mp2an
    eqeltri
end

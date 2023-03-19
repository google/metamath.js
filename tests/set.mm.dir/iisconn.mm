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
include "csconn.mm"
include "dfii2.mm"
include "cr.mm"
include "wcel.mm"
include "0re.mm"
include "1re.mm"
include "iccsconn.mm"
include "mp2an.mm"
include "eqeltri.mm"

theorem iisconn



  assert |- II e. SConn

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
    csconn
    dfii2
    cc0
    cr
    wcel
    c1
    cr
    wcel
    @0
    csconn
    wcel
    0re
    1re
    cc0
    c1
    iccsconn
    mp2an
    eqeltri
end

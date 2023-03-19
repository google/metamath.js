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
include "clly.mm"
include "dfii2.mm"
include "cr.mm"
include "wcel.mm"
include "0re.mm"
include "1re.mm"
include "iccllysconn.mm"
include "mp2an.mm"
include "eqeltri.mm"

theorem iillysconn



  assert |- II e. Locally SConn

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
    clly
    #
    dfii2
    cc0
    cr
    wcel
    c1
    cr
    wcel
    @0
    @1
    wcel
    0re
    1re
    cc0
    c1
    iccllysconn
    mp2an
    eqeltri
end

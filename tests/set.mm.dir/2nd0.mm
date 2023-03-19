include "c0.mm"
include "c2nd.mm"
include "cfv.mm"
include "csn.mm"
include "crn.mm"
include "cuni.mm"
include "2ndval.mm"
include "cdm.mm"
include "wceq.mm"
include "dmsn0.mm"
include "dm0rn0.mm"
include "mpbi.mm"
include "unieqi.mm"
include "uni0.mm"
include "3eqtri.mm"

theorem 2nd0



  assert |- ( 2nd ` (/) ) = (/)

  proof
    c0
    c2nd
    cfv
    c0
    csn
    #
    crn
    #
    cuni
    c0
    cuni
    c0
    c0
    2ndval
    @1
    c0
    @0
    cdm
    c0
    wceq
    @1
    c0
    wceq
    dmsn0
    @0
    dm0rn0
    mpbi
    unieqi
    uni0
    3eqtri
end

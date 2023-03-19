include "c0.mm"
include "c1st.mm"
include "cfv.mm"
include "csn.mm"
include "cdm.mm"
include "cuni.mm"
include "1stval.mm"
include "dmsn0.mm"
include "unieqi.mm"
include "uni0.mm"
include "3eqtri.mm"

theorem 1st0



  assert |- ( 1st ` (/) ) = (/)

  proof
    c0
    c1st
    cfv
    c0
    csn
    cdm
    #
    cuni
    c0
    cuni
    c0
    c0
    1stval
    @0
    c0
    dmsn0
    unieqi
    uni0
    3eqtri
end

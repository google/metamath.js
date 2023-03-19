include "cv.mm"
include "cdm.mm"
include "cuni.mm"
include "cdif.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cae.mm"
include "df-ae.mm"
include "relopabi.mm"

theorem relae
  let va: setvar a
  let vm: setvar m


  assert |- Rel ae

  proof
    vm
    cv
    #
    cdm
    cuni
    va
    cv
    cdif
    @0
    cfv
    cc0
    wceq
    va
    vm
    cae
    vm
    va
    df-ae
    relopabi
end

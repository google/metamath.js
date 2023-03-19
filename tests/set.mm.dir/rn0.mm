include "c0.mm"
include "cdm.mm"
include "wceq.mm"
include "crn.mm"
include "dm0.mm"
include "dm0rn0.mm"
include "mpbi.mm"

theorem rn0



  assert |- ran (/) = (/)

  proof
    c0
    cdm
    c0
    wceq
    c0
    crn
    c0
    wceq
    dm0
    c0
    dm0rn0
    mpbi
end

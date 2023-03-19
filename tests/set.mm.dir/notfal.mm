include "wfal.mm"
include "wn.mm"
include "fal.mm"
include "bitru.mm"

theorem notfal



  assert |- ( -. F. <-> T. )

  proof
    wfal
    wn
    fal
    bitru
end

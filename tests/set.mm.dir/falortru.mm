include "wfal.mm"
include "wtru.mm"
include "wo.mm"
include "tru.mm"
include "olci.mm"
include "bitru.mm"

theorem falortru



  assert |- ( ( F. \/ T. ) <-> T. )

  proof
    wfal
    wtru
    wo
    wtru
    wfal
    tru
    olci
    bitru
end

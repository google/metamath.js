include "wtru.mm"
include "wfal.mm"
include "wo.mm"
include "tru.mm"
include "orci.mm"
include "bitru.mm"

theorem truorfal



  assert |- ( ( T. \/ F. ) <-> T. )

  proof
    wtru
    wfal
    wo
    wtru
    wfal
    tru
    orci
    bitru
end

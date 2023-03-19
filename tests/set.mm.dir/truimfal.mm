include "wfal.mm"
include "wtru.mm"
include "wi.mm"
include "trut.mm"
include "bicomi.mm"

theorem truimfal



  assert |- ( ( T. -> F. ) <-> F. )

  proof
    wfal
    wtru
    wfal
    wi
    wfal
    trut
    bicomi
end

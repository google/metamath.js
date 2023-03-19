include "wfal.mm"
include "wi.mm"
include "id.mm"
include "bitru.mm"

theorem falimfal



  assert |- ( ( F. -> F. ) <-> T. )

  proof
    wfal
    wfal
    wi
    wfal
    id
    bitru
end

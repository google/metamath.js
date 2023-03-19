include "wfal.mm"
include "wtru.mm"
include "wi.mm"
include "falim.mm"
include "bitru.mm"

theorem falimtru



  assert |- ( ( F. -> T. ) <-> T. )

  proof
    wfal
    wtru
    wi
    wtru
    falim
    bitru
end

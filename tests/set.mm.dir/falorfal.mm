include "wfal.mm"
include "oridm.mm"

theorem falorfal



  assert |- ( ( F. \/ F. ) <-> F. )

  proof
    wfal
    oridm
end

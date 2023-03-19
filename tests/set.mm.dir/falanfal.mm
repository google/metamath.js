include "wfal.mm"
include "anidm.mm"

theorem falanfal



  assert |- ( ( F. /\ F. ) <-> F. )

  proof
    wfal
    anidm
end

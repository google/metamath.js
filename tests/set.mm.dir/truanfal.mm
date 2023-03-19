include "wfal.mm"
include "truan.mm"

theorem truanfal



  assert |- ( ( T. /\ F. ) <-> F. )

  proof
    wfal
    truan
end

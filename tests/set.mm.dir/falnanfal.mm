include "wfal.mm"
include "wnan.mm"
include "wn.mm"
include "wtru.mm"
include "nannot.mm"
include "notfal.mm"
include "bitr3i.mm"

theorem falnanfal



  assert |- ( ( F. -/\ F. ) <-> T. )

  proof
    wfal
    wfal
    wnan
    wfal
    wn
    wtru
    wfal
    nannot
    notfal
    bitr3i
end

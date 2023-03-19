include "wfal.mm"
include "wtru.mm"
include "wb.mm"
include "tbtru.mm"
include "bicomi.mm"

theorem falbitru



  assert |- ( ( F. <-> T. ) <-> F. )

  proof
    wfal
    wfal
    wtru
    wb
    wfal
    tbtru
    bicomi
end

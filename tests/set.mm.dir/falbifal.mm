include "wfal.mm"
include "wb.mm"
include "biid.mm"
include "bitru.mm"

theorem falbifal



  assert |- ( ( F. <-> F. ) <-> T. )

  proof
    wfal
    wfal
    wb
    wfal
    biid
    bitru
end

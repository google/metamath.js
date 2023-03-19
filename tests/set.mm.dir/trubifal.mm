include "wtru.mm"
include "wfal.mm"
include "wb.mm"
include "bicom.mm"
include "falbitru.mm"
include "bitri.mm"

theorem trubifal



  assert |- ( ( T. <-> F. ) <-> F. )

  proof
    wtru
    wfal
    wb
    wfal
    wtru
    wb
    wfal
    wtru
    wfal
    bicom
    falbitru
    bitri
end

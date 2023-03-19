include "wfal.mm"
include "wtru.mm"
include "wnan.mm"
include "nancom.mm"
include "trunanfal.mm"
include "bitri.mm"

theorem falnantru



  assert |- ( ( F. -/\ T. ) <-> T. )

  proof
    wfal
    wtru
    wnan
    wtru
    wfal
    wnan
    wtru
    wfal
    wtru
    nancom
    trunanfal
    bitri
end

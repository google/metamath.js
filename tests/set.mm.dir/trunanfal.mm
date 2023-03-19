include "wtru.mm"
include "wfal.mm"
include "wnan.mm"
include "wn.mm"
include "wa.mm"
include "df-nan.mm"
include "truanfal.mm"
include "xchbinx.mm"
include "notfal.mm"
include "bitri.mm"

theorem trunanfal



  assert |- ( ( T. -/\ F. ) <-> T. )

  proof
    wtru
    wfal
    wnan
    #
    wfal
    wn
    wtru
    @0
    wtru
    wfal
    wa
    wfal
    wtru
    wfal
    df-nan
    truanfal
    xchbinx
    notfal
    bitri
end

include "wtru.mm"
include "wfal.mm"
include "wxo.mm"
include "wn.mm"
include "wb.mm"
include "df-xor.mm"
include "trubifal.mm"
include "xchbinx.mm"
include "notfal.mm"
include "bitri.mm"

theorem truxorfal



  assert |- ( ( T. \/_ F. ) <-> T. )

  proof
    wtru
    wfal
    wxo
    #
    wfal
    wn
    wtru
    @0
    wtru
    wfal
    wb
    wfal
    wtru
    wfal
    df-xor
    trubifal
    xchbinx
    notfal
    bitri
end

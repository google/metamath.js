include "wfal.mm"
include "wxo.mm"
include "wtru.mm"
include "wn.mm"
include "wb.mm"
include "df-xor.mm"
include "falbifal.mm"
include "xchbinx.mm"
include "nottru.mm"
include "bitri.mm"

theorem falxorfal



  assert |- ( ( F. \/_ F. ) <-> F. )

  proof
    wfal
    wfal
    wxo
    #
    wtru
    wn
    wfal
    @0
    wfal
    wfal
    wb
    wtru
    wfal
    wfal
    df-xor
    falbifal
    xchbinx
    nottru
    bitri
end

include "wtru.mm"
include "wxo.mm"
include "wn.mm"
include "wfal.mm"
include "wb.mm"
include "df-xor.mm"
include "trubitru.mm"
include "xchbinx.mm"
include "nottru.mm"
include "bitri.mm"

theorem truxortru



  assert |- ( ( T. \/_ T. ) <-> F. )

  proof
    wtru
    wtru
    wxo
    #
    wtru
    wn
    wfal
    @0
    wtru
    wtru
    wb
    wtru
    wtru
    wtru
    df-xor
    trubitru
    xchbinx
    nottru
    bitri
end

include "wfal.mm"
include "wtru.mm"
include "wxo.mm"
include "xorcom.mm"
include "truxorfal.mm"
include "bitri.mm"

theorem falxortru



  assert |- ( ( F. \/_ T. ) <-> T. )

  proof
    wfal
    wtru
    wxo
    wtru
    wfal
    wxo
    wtru
    wfal
    wtru
    xorcom
    truxorfal
    bitri
end

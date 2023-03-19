include "wtru.mm"
include "wnan.mm"
include "wn.mm"
include "wfal.mm"
include "nannot.mm"
include "nottru.mm"
include "bitr3i.mm"

theorem trunantru



  assert |- ( ( T. -/\ T. ) <-> F. )

  proof
    wtru
    wtru
    wnan
    wtru
    wn
    wfal
    wtru
    nannot
    nottru
    bitr3i
end

include "cpnf.mm"
include "cxr.mm"
include "pnfxr.mm"
include "elexi.mm"

theorem pnfex



  assert |- +oo e. _V

  proof
    cpnf
    cxr
    pnfxr
    elexi
end

include "cple.mm"
include "c10.mm"
include "dfpleOLD.mm"
include "10nnOLD.mm"
include "ndxarg.mm"

theorem plendxOLD



  assert |- ( le ` ndx ) = 10

  proof
    cple
    c10
    dfpleOLD
    10nnOLD
    ndxarg
end

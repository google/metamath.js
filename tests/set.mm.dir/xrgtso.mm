include "cxr.mm"
include "clt.mm"
include "wor.mm"
include "ccnv.mm"
include "xrltso.mm"
include "cnvso.mm"
include "mpbi.mm"

theorem xrgtso



  assert |- `' < Or RR*

  proof
    cxr
    clt
    wor
    cxr
    clt
    ccnv
    wor
    xrltso
    cxr
    clt
    cnvso
    mpbi
end

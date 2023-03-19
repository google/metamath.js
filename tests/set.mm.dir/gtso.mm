include "cr.mm"
include "clt.mm"
include "wor.mm"
include "ccnv.mm"
include "ltso.mm"
include "cnvso.mm"
include "mpbi.mm"

theorem gtso



  assert |- `' < Or RR

  proof
    cr
    clt
    wor
    cr
    clt
    ccnv
    wor
    ltso
    cr
    clt
    cnvso
    mpbi
end

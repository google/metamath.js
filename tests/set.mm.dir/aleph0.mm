include "c0.mm"
include "cale.mm"
include "cfv.mm"
include "char.mm"
include "com.mm"
include "crdg.mm"
include "df-aleph.mm"
include "fveq1i.mm"
include "omex.mm"
include "rdg0.mm"
include "eqtri.mm"

theorem aleph0



  assert |- ( aleph ` (/) ) = _om

  proof
    c0
    cale
    cfv
    c0
    char
    com
    crdg
    #
    cfv
    com
    c0
    cale
    @0
    df-aleph
    fveq1i
    com
    char
    omex
    rdg0
    eqtri
end

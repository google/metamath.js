include "csset.mm"
include "wrel.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "cep.mm"
include "cdif.mm"
include "ctxp.mm"
include "crn.mm"
include "df-sset.mm"
include "difss.mm"
include "eqsstri.mm"
include "df-rel.mm"
include "mpbir.mm"

theorem relsset



  assert |- Rel SSet

  proof
    csset
    wrel
    csset
    cvv
    cvv
    cxp
    #
    wss
    csset
    @0
    cep
    cvv
    cep
    cdif
    ctxp
    crn
    #
    cdif
    @0
    df-sset
    @0
    @1
    difss
    eqsstri
    csset
    df-rel
    mpbir
end

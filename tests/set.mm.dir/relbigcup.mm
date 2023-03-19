include "cbigcup.mm"
include "wrel.mm"
include "cvv.mm"
include "cxp.mm"
include "cep.mm"
include "ctxp.mm"
include "ccom.mm"
include "csymdif.mm"
include "crn.mm"
include "cdif.mm"
include "relxp.mm"
include "reldif.mm"
include "ax-mp.mm"
include "df-bigcup.mm"
include "releqi.mm"
include "mpbir.mm"

theorem relbigcup



  assert |- Rel Bigcup

  proof
    cbigcup
    wrel
    cvv
    cvv
    cxp
    #
    cvv
    cep
    ctxp
    cep
    cep
    ccom
    cvv
    ctxp
    csymdif
    crn
    #
    cdif
    #
    wrel
    #
    @0
    wrel
    @3
    cvv
    cvv
    relxp
    @0
    @1
    reldif
    ax-mp
    cbigcup
    @2
    df-bigcup
    releqi
    mpbir
end

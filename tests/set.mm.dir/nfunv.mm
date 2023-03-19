include "cvv.mm"
include "wfun.mm"
include "wrel.mm"
include "c0.mm"
include "cxp.mm"
include "wcel.mm"
include "0nelxp.mm"
include "0ex.mm"
include "wss.mm"
include "df-rel.mm"
include "biimpi.mm"
include "sseld.mm"
include "mpi.mm"
include "mto.mm"
include "funrel.mm"

theorem nfunv



  assert |- -. Fun _V

  proof
    cvv
    wfun
    cvv
    wrel
    #
    @0
    c0
    cvv
    cvv
    cxp
    #
    wcel
    #
    cvv
    cvv
    0nelxp
    @0
    c0
    cvv
    wcel
    @2
    0ex
    @0
    cvv
    @1
    c0
    @0
    cvv
    @1
    wss
    cvv
    df-rel
    biimpi
    sseld
    mpi
    mto
    cvv
    funrel
    mto
end

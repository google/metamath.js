include "cmul.mm"
include "cvv.mm"
include "wcel.mm"
include "cvsca.mm"
include "cfv.mm"
include "wceq.mm"
include "mulex.mm"
include "cc.mm"
include "caddc.mm"
include "ccnfld.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cplusg.mm"
include "cpr.mm"
include "csca.mm"
include "cun.mm"
include "ctp.mm"
include "csn.mm"
include "qdass.mm"
include "eqtri.mm"
include "lmodvsca.mm"
include "eqcomd.mm"
include "ax-mp.mm"

theorem cnlmod4
  let cW: class W
  assume cnlmod.w: |- W = ( { <. ( Base ` ndx ) , CC >. , <. ( +g ` ndx ) , + >. } u. { <. ( Scalar ` ndx ) , CCfld >. , <. ( .s ` ndx ) , x. >. } )


  assert |- ( .s ` W ) = x.

  proof
    cmul
    cvv
    wcel
    #
    cW
    cvsca
    cfv
    #
    cmul
    wceq
    mulex
    @0
    cmul
    @1
    cc
    caddc
    cmul
    ccnfld
    cW
    cvv
    cW
    cnx
    cbs
    cfv
    cc
    cop
    #
    cnx
    cplusg
    cfv
    caddc
    cop
    #
    cpr
    cnx
    csca
    cfv
    ccnfld
    cop
    #
    cnx
    cvsca
    cfv
    cmul
    cop
    #
    cpr
    cun
    @2
    @3
    @4
    ctp
    @5
    csn
    cun
    cnlmod.w
    @2
    @3
    @4
    @5
    qdass
    eqtri
    lmodvsca
    eqcomd
    ax-mp
end

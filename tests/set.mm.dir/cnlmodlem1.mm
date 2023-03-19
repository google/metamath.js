include "cc.mm"
include "cvv.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "cnex.mm"
include "caddc.mm"
include "cmul.mm"
include "ccnfld.mm"
include "cnx.mm"
include "cop.mm"
include "cplusg.mm"
include "cpr.mm"
include "csca.mm"
include "cvsca.mm"
include "cun.mm"
include "ctp.mm"
include "csn.mm"
include "qdass.mm"
include "eqtri.mm"
include "lmodbase.mm"
include "eqcomd.mm"
include "ax-mp.mm"

theorem cnlmodlem1
  let cW: class W
  assume cnlmod.w: |- W = ( { <. ( Base ` ndx ) , CC >. , <. ( +g ` ndx ) , + >. } u. { <. ( Scalar ` ndx ) , CCfld >. , <. ( .s ` ndx ) , x. >. } )


  assert |- ( Base ` W ) = CC

  proof
    cc
    cvv
    wcel
    #
    cW
    cbs
    cfv
    #
    cc
    wceq
    cnex
    @0
    cc
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
    lmodbase
    eqcomd
    ax-mp
end

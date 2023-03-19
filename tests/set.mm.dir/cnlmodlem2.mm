include "caddc.mm"
include "cvv.mm"
include "wcel.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "addex.mm"
include "cc.mm"
include "cmul.mm"
include "ccnfld.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cpr.mm"
include "csca.mm"
include "cvsca.mm"
include "cun.mm"
include "ctp.mm"
include "csn.mm"
include "qdass.mm"
include "eqtri.mm"
include "lmodplusg.mm"
include "eqcomd.mm"
include "ax-mp.mm"

theorem cnlmodlem2
  let cW: class W
  assume cnlmod.w: |- W = ( { <. ( Base ` ndx ) , CC >. , <. ( +g ` ndx ) , + >. } u. { <. ( Scalar ` ndx ) , CCfld >. , <. ( .s ` ndx ) , x. >. } )


  assert |- ( +g ` W ) = +

  proof
    caddc
    cvv
    wcel
    #
    cW
    cplusg
    cfv
    #
    caddc
    wceq
    addex
    @0
    caddc
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
    lmodplusg
    eqcomd
    ax-mp
end

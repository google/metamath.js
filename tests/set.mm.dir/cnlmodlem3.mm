include "ccnfld.mm"
include "cvv.mm"
include "wcel.mm"
include "csca.mm"
include "cfv.mm"
include "wceq.mm"
include "cnfldex.mm"
include "cc.mm"
include "caddc.mm"
include "cmul.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cplusg.mm"
include "cpr.mm"
include "cvsca.mm"
include "cun.mm"
include "ctp.mm"
include "csn.mm"
include "qdass.mm"
include "eqtri.mm"
include "lmodsca.mm"
include "eqcomd.mm"
include "ax-mp.mm"

theorem cnlmodlem3
  let cW: class W
  assume cnlmod.w: |- W = ( { <. ( Base ` ndx ) , CC >. , <. ( +g ` ndx ) , + >. } u. { <. ( Scalar ` ndx ) , CCfld >. , <. ( .s ` ndx ) , x. >. } )


  assert |- ( Scalar ` W ) = CCfld

  proof
    ccnfld
    cvv
    wcel
    #
    cW
    csca
    cfv
    #
    ccnfld
    wceq
    cnfldex
    @0
    ccnfld
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
    lmodsca
    eqcomd
    ax-mp
end

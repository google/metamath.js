include "wcel.mm"
include "crglmod.mm"
include "cfv.mm"
include "cbs.mm"
include "csra.mm"
include "cnx.mm"
include "csca.mm"
include "cress.mm"
include "co.mm"
include "cop.mm"
include "csts.mm"
include "cvsca.mm"
include "cmulr.mm"
include "cip.mm"
include "wceq.mm"
include "rlmval.mm"
include "a1i.mm"
include "wss.mm"
include "ssid.mm"
include "sraval.mm"
include "mpan2.mm"
include "eqid.mm"
include "ressid.mm"
include "opeq2d.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "3eqtrd.mm"

theorem rlmval2
  let cW: class W
  let cX: class X


  assert |- ( W e. X -> ( ringLMod ` W ) = ( ( ( W sSet <. ( Scalar ` ndx ) , W >. ) sSet <. ( .s ` ndx ) , ( .r ` W ) >. ) sSet <. ( .i ` ndx ) , ( .r ` W ) >. ) )

  proof
    cW
    cX
    wcel
    #
    cW
    crglmod
    cfv
    #
    cW
    cbs
    cfv
    #
    cW
    csra
    cfv
    cfv
    #
    cW
    cnx
    csca
    cfv
    #
    cW
    @2
    cress
    co
    #
    cop
    #
    csts
    co
    #
    cnx
    cvsca
    cfv
    cW
    cmulr
    cfv
    #
    cop
    #
    csts
    co
    #
    cnx
    cip
    cfv
    @8
    cop
    #
    csts
    co
    #
    cW
    @4
    cW
    cop
    #
    csts
    co
    #
    @9
    csts
    co
    #
    @11
    csts
    co
    @1
    @3
    wceq
    @0
    cW
    rlmval
    a1i
    @0
    @2
    @2
    wss
    @3
    @12
    wceq
    @2
    ssid
    @2
    cX
    cW
    sraval
    mpan2
    @0
    @10
    @15
    @11
    csts
    @0
    @7
    @14
    @9
    csts
    @0
    @6
    @13
    cW
    csts
    @0
    @5
    cW
    @4
    @2
    cW
    cX
    @2
    eqid
    ressid
    opeq2d
    oveq2d
    oveq1d
    oveq1d
    3eqtrd
end

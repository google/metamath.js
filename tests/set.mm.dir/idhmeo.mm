include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "ccn.mm"
include "co.mm"
include "ccnv.mm"
include "chmeo.mm"
include "idcn.mm"
include "cnvresid.mm"
include "syl5eqel.mm"
include "ishmeo.mm"
include "sylanbrc.mm"

theorem idhmeo
  let cJ: class J
  let cX: class X


  assert |- ( J e. ( TopOn ` X ) -> ( _I |` X ) e. ( J Homeo J ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cid
    cX
    cres
    #
    cJ
    cJ
    ccn
    co
    #
    wcel
    @1
    ccnv
    #
    @2
    wcel
    @1
    cJ
    cJ
    chmeo
    co
    wcel
    cJ
    cX
    idcn
    #
    @0
    @3
    @1
    @2
    cX
    cnvresid
    @4
    syl5eqel
    @1
    cJ
    cJ
    ishmeo
    sylanbrc
end

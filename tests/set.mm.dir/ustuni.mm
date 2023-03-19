include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "cpw.mm"
include "wss.mm"
include "cuni.mm"
include "wceq.mm"
include "ustbasel.mm"
include "cv.mm"
include "wral.mm"
include "ustssxp.mm"
include "ralrimiva.mm"
include "pwssb.mm"
include "sylibr.mm"
include "elpwuni.mm"
include "biimpa.mm"
include "syl2anc.mm"

theorem ustuni
  let cU: class U
  let cX: class X
  let vu: setvar u


  assert |- ( U e. ( UnifOn ` X ) -> U. U = ( X X. X ) )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    cX
    cX
    cxp
    #
    cU
    wcel
    #
    cU
    @1
    cpw
    wss
    #
    cU
    cuni
    @1
    wceq
    #
    cU
    cX
    ustbasel
    @0
    vu
    cv
    #
    @1
    wss
    #
    vu
    cU
    wral
    @3
    @0
    @6
    vu
    cU
    cU
    @5
    cX
    ustssxp
    ralrimiva
    vu
    cU
    @1
    pwssb
    sylibr
    @2
    @3
    @4
    cU
    @1
    elpwuni
    biimpa
    syl2anc
end

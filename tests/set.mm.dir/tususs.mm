include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cunif.mm"
include "cuss.mm"
include "tusunif.mm"
include "cbs.mm"
include "cxp.mm"
include "cuni.mm"
include "wceq.mm"
include "ustuni.mm"
include "unieqd.mm"
include "tusbas.mm"
include "sqxpeqd.mm"
include "3eqtr3rd.mm"
include "eqid.mm"
include "ussid.mm"
include "syl.mm"
include "eqtrd.mm"

theorem tususs
  let cU: class U
  let cK: class K
  let cX: class X
  let vu: setvar u
  assume tuslem.k: |- K = ( toUnifSp ` U )


  assert |- ( U e. ( UnifOn ` X ) -> U = ( UnifSt ` K ) )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    cU
    cK
    cunif
    cfv
    #
    cK
    cuss
    cfv
    #
    cU
    cK
    cX
    tuslem.k
    tusunif
    #
    @0
    cK
    cbs
    cfv
    #
    @4
    cxp
    #
    @1
    cuni
    #
    wceq
    @1
    @2
    wceq
    @0
    cU
    cuni
    cX
    cX
    cxp
    @6
    @5
    cU
    cX
    ustuni
    @0
    cU
    @1
    @3
    unieqd
    @0
    cX
    @4
    cU
    cK
    cX
    tuslem.k
    tusbas
    sqxpeqd
    3eqtr3rd
    @4
    @1
    cK
    @4
    eqid
    @1
    eqid
    ussid
    syl
    eqtrd
end

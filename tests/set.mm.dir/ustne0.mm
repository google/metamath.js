include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "c0.mm"
include "wne.mm"
include "ustbasel.mm"
include "ne0i.mm"
include "syl.mm"

theorem ustne0
  let cU: class U
  let cX: class X


  assert |- ( U e. ( UnifOn ` X ) -> U =/= (/) )

  proof
    cU
    cX
    cust
    cfv
    wcel
    cX
    cX
    cxp
    #
    cU
    wcel
    cU
    c0
    wne
    cU
    cX
    ustbasel
    cU
    @0
    ne0i
    syl
end

include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cutop.mm"
include "ctop.mm"
include "cuni.mm"
include "wceq.mm"
include "ctopon.mm"
include "utoptop.mm"
include "utopbas.mm"
include "istopon.mm"
include "sylanbrc.mm"

theorem utoptopon
  let cU: class U
  let cX: class X


  assert |- ( U e. ( UnifOn ` X ) -> ( unifTop ` U ) e. ( TopOn ` X ) )

  proof
    cU
    cX
    cust
    cfv
    wcel
    cU
    cutop
    cfv
    #
    ctop
    wcel
    cX
    @0
    cuni
    wceq
    @0
    cX
    ctopon
    cfv
    wcel
    cU
    cX
    utoptop
    cU
    cX
    utopbas
    cX
    @0
    istopon
    sylanbrc
end

include "ccring.mm"
include "wcel.mm"
include "crngo.mm"
include "ccm2.mm"
include "iscrngo.mm"
include "simplbi.mm"

theorem crngorngo
  let cR: class R


  assert |- ( R e. CRingOps -> R e. RingOps )

  proof
    cR
    ccring
    wcel
    cR
    crngo
    wcel
    cR
    ccm2
    wcel
    cR
    iscrngo
    simplbi
end

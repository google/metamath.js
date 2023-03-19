include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cutop.mm"
include "ctopn.mm"
include "cbs.mm"
include "wceq.mm"
include "cunif.mm"
include "tuslem.mm"
include "simp3d.mm"
include "syl5eq.mm"

theorem tustopn
  let cU: class U
  let cJ: class J
  let cK: class K
  let cX: class X
  let vu: setvar u
  assume tuslem.k: |- K = ( toUnifSp ` U )
  assume tustopn.j: |- J = ( unifTop ` U )


  assert |- ( U e. ( UnifOn ` X ) -> J = ( TopOpen ` K ) )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    cJ
    cU
    cutop
    cfv
    #
    cK
    ctopn
    cfv
    #
    tustopn.j
    @0
    cX
    cK
    cbs
    cfv
    wceq
    cU
    cK
    cunif
    cfv
    wceq
    @1
    @2
    wceq
    cU
    cK
    cX
    tuslem.k
    tuslem
    simp3d
    syl5eq
end

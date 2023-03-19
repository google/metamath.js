include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cbs.mm"
include "wceq.mm"
include "cunif.mm"
include "cutop.mm"
include "ctopn.mm"
include "tuslem.mm"
include "simp1d.mm"

theorem tusbas
  let cU: class U
  let cK: class K
  let cX: class X
  let vu: setvar u
  assume tuslem.k: |- K = ( toUnifSp ` U )


  assert |- ( U e. ( UnifOn ` X ) -> X = ( Base ` K ) )

  proof
    cU
    cX
    cust
    cfv
    wcel
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
    cU
    cutop
    cfv
    cK
    ctopn
    cfv
    wceq
    cU
    cK
    cX
    tuslem.k
    tuslem
    simp1d
end

include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cuss.mm"
include "cbs.mm"
include "ctopn.mm"
include "cutop.mm"
include "wceq.mm"
include "cusp.mm"
include "id.mm"
include "tususs.mm"
include "tusbas.mm"
include "fveq2d.mm"
include "3eltr3d.mm"
include "cunif.mm"
include "tusunif.mm"
include "tuslem.mm"
include "simp3d.mm"
include "eqtr3d.mm"
include "3eqtr3d.mm"
include "eqid.mm"
include "isusp.mm"
include "sylanbrc.mm"

theorem tususp
  let cU: class U
  let cK: class K
  let cX: class X
  let vu: setvar u
  assume tuslem.k: |- K = ( toUnifSp ` U )


  assert |- ( U e. ( UnifOn ` X ) -> K e. UnifSp )

  proof
    cU
    cX
    cust
    cfv
    #
    wcel
    #
    cK
    cuss
    cfv
    #
    cK
    cbs
    cfv
    #
    cust
    cfv
    #
    wcel
    cK
    ctopn
    cfv
    #
    @2
    cutop
    cfv
    #
    wceq
    cK
    cusp
    wcel
    @1
    cU
    @0
    @2
    @4
    @1
    id
    cU
    cK
    cX
    tuslem.k
    tususs
    #
    @1
    cX
    @3
    cust
    cU
    cK
    cX
    tuslem.k
    tusbas
    fveq2d
    3eltr3d
    @1
    cU
    cutop
    cfv
    #
    cK
    cunif
    cfv
    #
    cutop
    cfv
    @5
    @6
    @1
    cU
    @9
    cutop
    cU
    cK
    cX
    tuslem.k
    tusunif
    #
    fveq2d
    @1
    cX
    @3
    wceq
    cU
    @9
    wceq
    @8
    @5
    wceq
    cU
    cK
    cX
    tuslem.k
    tuslem
    simp3d
    @1
    @9
    @2
    cutop
    @1
    cU
    @9
    @2
    @10
    @7
    eqtr3d
    fveq2d
    3eqtr3d
    @3
    @2
    @5
    cK
    @3
    eqid
    @2
    eqid
    @5
    eqid
    isusp
    sylanbrc
end

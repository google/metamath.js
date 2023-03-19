include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "ctopn.mm"
include "cbs.mm"
include "ctopon.mm"
include "ctps.mm"
include "cutop.mm"
include "utoptopon.mm"
include "eqid.mm"
include "tustopn.mm"
include "tusbas.mm"
include "fveq2d.mm"
include "3eltr3d.mm"
include "istps.mm"
include "sylibr.mm"

theorem tustps
  let cU: class U
  let cK: class K
  let cX: class X
  let vu: setvar u
  assume tuslem.k: |- K = ( toUnifSp ` U )


  assert |- ( U e. ( UnifOn ` X ) -> K e. TopSp )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    cK
    ctopn
    cfv
    #
    cK
    cbs
    cfv
    #
    ctopon
    cfv
    #
    wcel
    cK
    ctps
    wcel
    @0
    cU
    cutop
    cfv
    #
    cX
    ctopon
    cfv
    @1
    @3
    cU
    cX
    utoptopon
    cU
    @4
    cK
    cX
    tuslem.k
    @4
    eqid
    tustopn
    @0
    cX
    @2
    ctopon
    cU
    cK
    cX
    tuslem.k
    tusbas
    fveq2d
    3eltr3d
    @2
    @1
    cK
    @2
    eqid
    @1
    eqid
    istps
    sylibr
end
